// Command capacitycheck runs isolated capacity measurements against the real
// HTTP server binary (cmd/voiceservice, unmodified) and records memory,
// latency, and render-job outcome evidence as JSON. Each scenario starts a
// fresh server child process with its own temporary data directory, drives it
// over HTTP, samples the child's RSS from /proc, and verifies terminal job
// states plus downloaded output digests. It exists to support the capacity
// and degradation manual in docs/capacity-manual.md and does not change any
// production package.
package main

import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"math"
	"net"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"

	"voice-timeline-renderer/internal/audiocodec"
	"voice-timeline-renderer/internal/domain"
	"voice-timeline-renderer/internal/service"
)

const (
	mib              = 1 << 20
	maxSourceBytes   = 32 * mib
	maxOutputFrames  = 48000 * 180
	maxSpans         = 64
	budgetMiB        = 512.0
	commitCeilingMiB = 384.0 // 75% of budget: headroom for kernel, fragmentation, GC jitter
)

// ---------- evidence schema ----------

type StepRecord struct {
	Name      string  `json:"name"`
	Method    string  `json:"method"`
	Path      string  `json:"path"`
	Status    int     `json:"status"`
	LatencyMS float64 `json:"latency_ms"`
	BytesUp   int64   `json:"bytes_up,omitempty"`
	BytesDown int64   `json:"bytes_down,omitempty"`
	ErrorCode string  `json:"error_code,omitempty"`
	Note      string  `json:"note,omitempty"`
}

type LatencyStat struct {
	N      int     `json:"n"`
	MinMS  float64 `json:"min_ms"`
	P50MS  float64 `json:"p50_ms"`
	P95MS  float64 `json:"p95_ms"`
	MaxMS  float64 `json:"max_ms"`
	MeanMS float64 `json:"mean_ms"`
}

type RenderFacts struct {
	JobID            string   `json:"job_id"`
	PUTStatus        int      `json:"put_status,omitempty"`
	PUTLatencyMS     float64  `json:"put_latency_ms,omitempty"`
	PUTNote          string   `json:"put_note,omitempty"`
	ObservedStates   []string `json:"observed_states"`
	TerminalState    string   `json:"terminal_state"`
	JobErrorCode     string   `json:"job_error_code,omitempty"`
	JobErrorMessage  string   `json:"job_error_message,omitempty"`
	ReceiptStatus    int      `json:"receipt_status"`
	ReceiptDigest    string   `json:"receipt_digest,omitempty"`
	JobReceiptDigest string   `json:"job_receipt_digest,omitempty"`
	OutputStatus     int      `json:"output_status"`
	OutputErrorCode  string   `json:"output_error_code,omitempty"`
	OutputBytes      int64    `json:"output_bytes,omitempty"`
	OutputSHA256     string   `json:"output_sha256,omitempty"`
	DigestMatch      bool     `json:"digest_match"`
}

type MemoryFacts struct {
	IdleRSSMB  float64            `json:"idle_rss_mb"`
	PeakRSSMB  float64            `json:"peak_rss_mb_polled"`
	VmHWMMb    float64            `json:"vmhwm_mb"`
	PhaseHWMMb map[string]float64 `json:"phase_hwm_mb,omitempty"`
}

type ScenarioRecord struct {
	ID             string                 `json:"id"`
	Purpose        string                 `json:"purpose"`
	LimitsEngaged  map[string]any         `json:"limits_engaged"`
	GOMEMLIMIT     string                 `json:"gomemlimit,omitempty"`
	Expectation    string                 `json:"expectation"`
	ExpectationMet bool                   `json:"expectation_met"`
	Steps          []StepRecord           `json:"steps"`
	LatencyStats   map[string]LatencyStat `json:"latency_stats,omitempty"`
	Render         *RenderFacts           `json:"render,omitempty"`
	Memory         MemoryFacts            `json:"memory"`
	WallMS         float64                `json:"wall_ms"`
	Findings       []string               `json:"findings,omitempty"`
	Verdict        string                 `json:"verdict"`
	VerdictReasons []string               `json:"verdict_reasons,omitempty"`
}

type Evidence struct {
	Tool             string           `json:"tool"`
	StartedAt        string           `json:"started_at"`
	Host             map[string]any   `json:"host"`
	ServerBinary     string           `json:"server_binary"`
	ServerSHA256     string           `json:"server_sha256"`
	GitHead          string           `json:"git_head,omitempty"`
	BudgetMiB        float64          `json:"budget_mib"`
	CommitCeilingMiB float64          `json:"commit_ceiling_mib"`
	Scenarios        []ScenarioRecord `json:"scenarios"`
}

// ---------- scenario bookkeeping ----------

type scenario struct {
	mu      sync.Mutex
	rec     ScenarioRecord
	reasons []string
}

func newScenario(id, purpose string, limits map[string]any, expectation string) *scenario {
	return &scenario{
		rec: ScenarioRecord{
			ID:            id,
			Purpose:       purpose,
			LimitsEngaged: limits,
			Expectation:   expectation,
			Steps:         []StepRecord{},
			LatencyStats:  map[string]LatencyStat{},
		},
	}
}

func (sc *scenario) addStep(step StepRecord) {
	sc.mu.Lock()
	defer sc.mu.Unlock()
	sc.rec.Steps = append(sc.rec.Steps, step)
}

// reason records a deployability-affecting fact; any reason forces a gap verdict.
func (sc *scenario) reason(format string, args ...any) {
	sc.mu.Lock()
	defer sc.mu.Unlock()
	sc.reasons = append(sc.reasons, fmt.Sprintf(format, args...))
}

// finding records neutral evidence that does not by itself change the verdict.
func (sc *scenario) finding(format string, args ...any) {
	sc.mu.Lock()
	defer sc.mu.Unlock()
	sc.rec.Findings = append(sc.rec.Findings, fmt.Sprintf(format, args...))
}

func (sc *scenario) lastErrorCode() string {
	sc.mu.Lock()
	defer sc.mu.Unlock()
	if len(sc.rec.Steps) == 0 {
		return ""
	}
	return sc.rec.Steps[len(sc.rec.Steps)-1].ErrorCode
}

type abortScenario struct{ msg string }

func (sc *scenario) fatalf(format string, args ...any) {
	panic(abortScenario{msg: fmt.Sprintf(format, args...)})
}

// ---------- server child process ----------

type serverProc struct {
	cmd     *exec.Cmd
	baseURL string
	dataDir string

	mu        sync.Mutex
	peakRSSkB int64
	stopPoll  chan struct{}
	pollDone  chan struct{}
	termOnce  sync.Once
}

func readVM(pid int) (rssKB, hwmKB int64, err error) {
	data, err := os.ReadFile(fmt.Sprintf("/proc/%d/status", pid))
	if err != nil {
		return 0, 0, err
	}
	for _, line := range strings.Split(string(data), "\n") {
		fields := strings.Fields(line)
		if len(fields) != 3 {
			continue
		}
		value, convErr := strconv.ParseInt(fields[1], 10, 64)
		if convErr != nil {
			continue
		}
		switch fields[0] {
		case "VmRSS:":
			rssKB = value
		case "VmHWM:":
			hwmKB = value
		}
	}
	return rssKB, hwmKB, nil
}

func startServer(binary, gomemlimit string) (*serverProc, error) {
	dataDir, err := os.MkdirTemp("", "capacity-data-*")
	if err != nil {
		return nil, err
	}
	proc, err := startServerOnDir(binary, gomemlimit, dataDir)
	if err != nil {
		_ = os.RemoveAll(dataDir)
		return nil, err
	}
	return proc, nil
}

func startServerOnDir(binary, gomemlimit, dataDir string) (*serverProc, error) {
	listener, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		return nil, err
	}
	port := listener.Addr().(*net.TCPAddr).Port
	_ = listener.Close()

	cmd := exec.Command(binary, "-addr", fmt.Sprintf("127.0.0.1:%d", port), "-data", dataDir)
	cmd.Env = os.Environ()
	if gomemlimit != "" {
		cmd.Env = append(cmd.Env, "GOMEMLIMIT="+gomemlimit)
	}
	cmd.Stdout = io.Discard
	cmd.Stderr = io.Discard
	if err := cmd.Start(); err != nil {
		return nil, err
	}
	proc := &serverProc{
		cmd:      cmd,
		baseURL:  fmt.Sprintf("http://127.0.0.1:%d", port),
		dataDir:  dataDir,
		stopPoll: make(chan struct{}),
		pollDone: make(chan struct{}),
	}
	go proc.pollLoop()

	deadline := time.Now().Add(15 * time.Second)
	for {
		resp, err := http.Get(proc.baseURL + "/healthz")
		if err == nil {
			_ = resp.Body.Close()
			if resp.StatusCode == http.StatusOK {
				return proc, nil
			}
		}
		if time.Now().After(deadline) {
			proc.Shutdown()
			return nil, fmt.Errorf("server did not become healthy")
		}
		time.Sleep(50 * time.Millisecond)
	}
}

func (proc *serverProc) pollLoop() {
	defer close(proc.pollDone)
	ticker := time.NewTicker(10 * time.Millisecond)
	defer ticker.Stop()
	for {
		select {
		case <-proc.stopPoll:
			return
		case <-ticker.C:
			rss, _, err := readVM(proc.cmd.Process.Pid)
			if err != nil {
				continue
			}
			proc.mu.Lock()
			if rss > proc.peakRSSkB {
				proc.peakRSSkB = rss
			}
			proc.mu.Unlock()
		}
	}
}

func (proc *serverProc) currentRSSkB() int64 {
	rss, _, err := readVM(proc.cmd.Process.Pid)
	if err != nil {
		return 0
	}
	return rss
}

func (proc *serverProc) hwmKB() int64 {
	_, hwm, err := readVM(proc.cmd.Process.Pid)
	if err != nil {
		return 0
	}
	return hwm
}

func (proc *serverProc) peakPolledkB() int64 {
	proc.mu.Lock()
	defer proc.mu.Unlock()
	return proc.peakRSSkB
}

// Shutdown terminates the server gracefully (SIGINT, like production deploys).
// The data directory is left on disk; call RemoveData to clean it up.
func (proc *serverProc) Shutdown() {
	proc.terminate(os.Interrupt)
}

// Kill terminates the server with SIGKILL to simulate a hard memory-enforcement
// event (for example a cgroup OOM kill). The data directory is left on disk.
func (proc *serverProc) Kill() {
	proc.terminate(os.Kill)
}

func (proc *serverProc) terminate(sig os.Signal) {
	proc.termOnce.Do(func() {
		close(proc.stopPoll)
		<-proc.pollDone
		if proc.cmd.Process != nil {
			_ = proc.cmd.Process.Signal(sig)
		}
		done := make(chan struct{})
		go func() {
			_ = proc.cmd.Wait()
			close(done)
		}()
		select {
		case <-done:
		case <-time.After(10 * time.Second):
			_ = proc.cmd.Process.Kill()
			<-done
		}
	})
}

func (proc *serverProc) RemoveData() {
	_ = os.RemoveAll(proc.dataDir)
}

// ---------- HTTP client ----------

type client struct {
	hc   *http.Client
	base string
}

type stepOutcome struct {
	status    int
	body      []byte
	latency   time.Duration
	clientErr error
}

func newClient(base string) *client {
	return &client{hc: &http.Client{}, base: base}
}

func errorCodeOf(body []byte) string {
	var envelope struct {
		Error struct {
			Code string `json:"code"`
		} `json:"error"`
	}
	if err := json.Unmarshal(body, &envelope); err != nil {
		return ""
	}
	return envelope.Error.Code
}

func (c *client) doRaw(method, path string, body io.Reader, bytesUp int64, timeout time.Duration) stepOutcome {
	ctx, cancel := context.WithTimeout(context.Background(), timeout)
	defer cancel()
	request, err := http.NewRequestWithContext(ctx, method, c.base+path, body)
	if err != nil {
		return stepOutcome{clientErr: err}
	}
	if bytesUp >= 0 {
		request.ContentLength = bytesUp
	}
	request.Header.Set("Content-Type", "application/json")
	start := time.Now()
	response, err := c.hc.Do(request)
	if err != nil {
		return stepOutcome{clientErr: err, latency: time.Since(start)}
	}
	defer response.Body.Close()
	payload, readErr := io.ReadAll(response.Body)
	if readErr != nil {
		return stepOutcome{status: response.StatusCode, clientErr: readErr, latency: time.Since(start)}
	}
	return stepOutcome{status: response.StatusCode, body: payload, latency: time.Since(start)}
}

func (c *client) record(sc *scenario, name, method, path string, bytesUp int64, outcome stepOutcome) {
	step := StepRecord{
		Name:      name,
		Method:    method,
		Path:      path,
		Status:    outcome.status,
		LatencyMS: float64(outcome.latency) / float64(time.Millisecond),
		BytesUp:   bytesUp,
		BytesDown: int64(len(outcome.body)),
	}
	if outcome.clientErr != nil {
		step.Note = "client_error: " + outcome.clientErr.Error()
	}
	if outcome.status >= 400 {
		step.ErrorCode = errorCodeOf(outcome.body)
	}
	sc.addStep(step)
}

func (c *client) step(sc *scenario, name, method, path string, payload any, timeout time.Duration) (int, []byte) {
	var reader io.Reader
	var bytesUp int64
	if payload != nil {
		encoded, err := json.Marshal(payload)
		if err != nil {
			sc.fatalf("marshal %s: %v", name, err)
		}
		reader = bytes.NewReader(encoded)
		bytesUp = int64(len(encoded))
	}
	outcome := c.doRaw(method, path, reader, bytesUp, timeout)
	c.record(sc, name, method, path, bytesUp, outcome)
	return outcome.status, outcome.body
}

func (c *client) expectStatus(sc *scenario, name string, got, want int) {
	if got != want {
		sc.reason("step %s returned status %d, want %d", name, got, want)
	}
}

// ---------- request helpers ----------

func (c *client) putSource(sc *scenario, id string, wav []byte, timeout time.Duration) (int, domain.SourceAsset) {
	status, body := c.step(sc, "put_source:"+id, "PUT", "/v1/sources/"+id, service.SourceWriteRequest{
		Name:      "capacity probe " + id,
		WAVBase64: base64.StdEncoding.EncodeToString(wav),
	}, timeout)
	var asset domain.SourceAsset
	if status == 200 || status == 201 {
		if err := json.Unmarshal(body, &asset); err != nil {
			sc.fatalf("decode source %s: %v", id, err)
		}
	}
	return status, asset
}

func (c *client) putTimeline(sc *scenario, id string, sampleRate, channels int, spans []domain.TimelineSpan) (int, domain.Timeline) {
	status, body := c.step(sc, "put_timeline:"+id, "PUT", "/v1/timelines/"+id, service.TimelineWriteRequest{
		Name:           "capacity probe " + id,
		SampleRate:     sampleRate,
		OutputChannels: channels,
		TargetPeakDBFS: -1,
		Spans:          spans,
	}, 60*time.Second)
	var plan domain.Timeline
	if status == 200 || status == 201 {
		if err := json.Unmarshal(body, &plan); err != nil {
			sc.fatalf("decode timeline %s: %v", id, err)
		}
	}
	return status, plan
}

// verifyRender polls the durable job record to its terminal state and then
// collects receipt and output-download facts.
func (c *client) verifyRender(sc *scenario, renderID string, pollDeadline time.Duration) RenderFacts {
	facts := RenderFacts{JobID: renderID, ObservedStates: []string{}}
	deadline := time.Now().Add(pollDeadline)
	lastState := ""
	for {
		status, body := c.step(sc, "get_render:"+renderID, "GET", "/v1/renders/"+renderID, nil, 30*time.Second)
		if status == 200 {
			var job domain.RenderJob
			if err := json.Unmarshal(body, &job); err == nil {
				state := string(job.State)
				if state != lastState {
					facts.ObservedStates = append(facts.ObservedStates, state)
					lastState = state
				}
				if job.State == domain.RenderCompleted || job.State == domain.RenderFailed {
					facts.TerminalState = state
					facts.JobReceiptDigest = job.ReceiptDigest
					if job.Error != nil {
						facts.JobErrorCode = job.Error.Code
						facts.JobErrorMessage = job.Error.Message
					}
					break
				}
			}
		}
		if time.Now().After(deadline) {
			facts.TerminalState = "poll_deadline_exceeded"
			sc.reason("render %s did not reach a terminal state within %s", renderID, pollDeadline)
			break
		}
		time.Sleep(200 * time.Millisecond)
	}

	rStatus, rBody := c.step(sc, "get_receipt:"+renderID, "GET", "/v1/renders/"+renderID+"/receipt", nil, 60*time.Second)
	facts.ReceiptStatus = rStatus
	if rStatus == 200 {
		var receipt domain.RenderReceipt
		if err := json.Unmarshal(rBody, &receipt); err == nil {
			facts.ReceiptDigest = receipt.Output.Digest
		}
	}
	oStatus, oBody := c.step(sc, "get_output:"+renderID, "GET", "/v1/renders/"+renderID+"/output", nil, 120*time.Second)
	facts.OutputStatus = oStatus
	if oStatus == 200 {
		sum := sha256.Sum256(oBody)
		facts.OutputSHA256 = hex.EncodeToString(sum[:])
		facts.OutputBytes = int64(len(oBody))
		facts.DigestMatch = facts.ReceiptDigest != "" && facts.OutputSHA256 == facts.ReceiptDigest
	} else {
		facts.OutputErrorCode = errorCodeOf(oBody)
	}
	sc.rec.Render = &facts
	return facts
}

func (c *client) renderAndVerify(sc *scenario, renderID, timelineID string, putTimeout, pollDeadline time.Duration) RenderFacts {
	body := mustJSON(service.RenderWriteRequest{TimelineID: timelineID})
	outcome := c.doRaw("PUT", "/v1/renders/"+renderID, bytes.NewReader(body), int64(len(body)), putTimeout)
	c.record(sc, "put_render:"+renderID, "PUT", "/v1/renders/"+renderID, int64(len(body)), outcome)
	facts := c.verifyRender(sc, renderID, pollDeadline)
	facts.PUTStatus = outcome.status
	facts.PUTLatencyMS = float64(outcome.latency) / float64(time.Millisecond)
	if outcome.clientErr != nil {
		facts.PUTNote = "client_error: " + outcome.clientErr.Error()
	}
	sc.rec.Render = &facts
	return facts
}

// ---------- WAV generation ----------

func sineWAV(sampleRate, channels int, frames int64, frequency, amplitude float64) []byte {
	samples := make([]float32, int(frames)*channels)
	for frame := int64(0); frame < frames; frame++ {
		seconds := float64(frame) / float64(sampleRate)
		value := float32(math.Sin(2*math.Pi*frequency*seconds) * amplitude)
		for channel := 0; channel < channels; channel++ {
			samples[int(frame)*channels+channel] = value
		}
	}
	encoded, err := audiocodec.EncodePCM16(sampleRate, channels, samples)
	if err != nil {
		panic(err)
	}
	return encoded
}

func framesForBytes(targetBytes int64, channels int) int64 {
	return (targetBytes - 44) / (2 * int64(channels))
}

func mustJSON(value any) []byte {
	encoded, err := json.Marshal(value)
	if err != nil {
		panic(err)
	}
	return encoded
}

// ---------- scenario runner ----------

type runEnv struct {
	binary   string
	scenario *scenario
}

func (env *runEnv) withServer(gomemlimit string, fn func(c *client, proc *serverProc)) {
	sc := env.scenario
	sc.rec.GOMEMLIMIT = gomemlimit
	started := time.Now()
	proc, err := startServer(env.binary, gomemlimit)
	if err != nil {
		sc.reason("server start failed: %v", err)
		sc.rec.WallMS = float64(time.Since(started)) / float64(time.Millisecond)
		return
	}
	defer func() {
		if recovered := recover(); recovered != nil {
			if abort, ok := recovered.(abortScenario); ok {
				sc.reason("scenario aborted: %s", abort.msg)
			} else {
				panic(recovered)
			}
		}
		sc.rec.Memory.PeakRSSMB = float64(proc.peakPolledkB()) / 1024
		sc.rec.Memory.VmHWMMb = float64(proc.hwmKB()) / 1024
		sc.rec.WallMS = float64(time.Since(started)) / float64(time.Millisecond)
		proc.Shutdown()
		proc.RemoveData()
	}()
	sc.rec.Memory.IdleRSSMB = float64(proc.currentRSSkB()) / 1024
	fn(newClient(proc.baseURL), proc)
}

func (sc *scenario) finalize() {
	if len(sc.reasons) > 0 {
		sc.rec.Verdict = "gap"
	} else if sc.rec.Memory.VmHWMMb > budgetMiB {
		sc.reason("peak RSS %.1f MiB exceeds the %.0f MiB budget", sc.rec.Memory.VmHWMMb, budgetMiB)
		sc.rec.Verdict = "gap"
	} else if sc.rec.Memory.VmHWMMb > commitCeilingMiB {
		sc.rec.Verdict = "boundary"
		sc.reason("peak RSS %.1f MiB is above the %.0f MiB commit ceiling", sc.rec.Memory.VmHWMMb, commitCeilingMiB)
	} else {
		sc.rec.Verdict = "commit"
	}
	if sc.rec.Render != nil {
		facts := sc.rec.Render
		if facts.TerminalState != string(domain.RenderCompleted) {
			sc.rec.Verdict = "gap"
			sc.reason("render %s ended in state %q (job error %q)", facts.JobID, facts.TerminalState, facts.JobErrorCode)
		} else if !facts.DigestMatch {
			sc.rec.Verdict = "gap"
			sc.reason("render %s output digest does not match the receipt", facts.JobID)
		}
	}
	sc.rec.ExpectationMet = strings.Contains(strings.ToLower(sc.rec.Expectation), sc.rec.Verdict)
	sc.rec.VerdictReasons = sc.reasons
}

// ---------- scenarios ----------

type scenarioFunc func(env *runEnv, sc *scenario)

func scenarioLimitsEnforcement(env *runEnv, sc *scenario) {
	env.withServer("", func(c *client, proc *serverProc) {
		// Source payload exactly at MaxSourceBytes must pass.
		atLimit := sineWAV(48000, 1, framesForBytes(maxSourceBytes, 1), 440, 0.3)
		status, _ := c.putSource(sc, "src_limit_exact", atLimit, 120*time.Second)
		c.expectStatus(sc, "source_at_limit", status, 201)
		sc.finding("source at exactly 32 MiB accepted (status %d)", status)

		// One frame over MaxSourceBytes must be rejected by the service.
		overLimit := sineWAV(48000, 1, framesForBytes(maxSourceBytes, 1)+1, 440, 0.3)
		status, _ = c.putSource(sc, "src_limit_over", overLimit, 120*time.Second)
		c.expectStatus(sc, "source_over_limit", status, 413)
		if got := sc.lastErrorCode(); got != "source_too_large" {
			sc.reason("over-limit source error code = %q, want source_too_large", got)
		}
		sc.finding("source one frame over 32 MiB rejected: status %d code %s", status, sc.lastErrorCode())

		// A request body beyond MaxSourceRequestBytes must be rejected by the HTTP layer.
		bigPayload := sineWAV(48000, 1, framesForBytes(37*mib, 1), 440, 0.3)
		status, _ = c.putSource(sc, "src_request_over", bigPayload, 180*time.Second)
		c.expectStatus(sc, "request_over_limit", status, 413)
		if got := sc.lastErrorCode(); got != "request_too_large" {
			sc.reason("oversized request error code = %q, want request_too_large", got)
		}
		sc.finding("~49.4 MiB request body rejected: status %d code %s", status, sc.lastErrorCode())

		// Span count above MaxSpans must be rejected.
		tiny := sineWAV(48000, 1, 48000, 440, 0.3)
		status, _ = c.putSource(sc, "src_tiny", tiny, 60*time.Second)
		c.expectStatus(sc, "tiny_source", status, 201)
		spans := make([]domain.TimelineSpan, 0, maxSpans+1)
		for index := 0; index < maxSpans+1; index++ {
			spans = append(spans, domain.TimelineSpan{SourceID: "src_tiny", SourceStartFrame: 0, SourceEndFrame: 48000})
		}
		status, _ = c.putTimeline(sc, "tl_spans_over", 48000, 2, spans)
		c.expectStatus(sc, "spans_over_limit", status, 422)
		if got := sc.lastErrorCode(); got != "invalid_span_count" {
			sc.reason("span overflow error code = %q, want invalid_span_count", got)
		}
		sc.finding("65-span timeline rejected: status %d code %s", status, sc.lastErrorCode())

		// Timeline output beyond MaxOutputFrames must be rejected at compose time.
		longSource := sineWAV(48000, 1, maxOutputFrames+1, 440, 0.3)
		status, _ = c.putSource(sc, "src_long", longSource, 120*time.Second)
		c.expectStatus(sc, "long_source", status, 201)
		status, _ = c.putTimeline(sc, "tl_frames_over", 48000, 2, []domain.TimelineSpan{
			{SourceID: "src_long", SourceStartFrame: 0, SourceEndFrame: maxOutputFrames + 1},
		})
		c.expectStatus(sc, "frames_over_limit", status, 413)
		if got := sc.lastErrorCode(); got != "timeline_too_long" {
			sc.reason("frame overflow error code = %q, want timeline_too_long", got)
		}
		sc.finding("timeline one frame over the output cap rejected: status %d code %s", status, sc.lastErrorCode())
	})
}

func scenarioBaselineOrdinary(env *runEnv, sc *scenario) {
	env.withServer("", func(c *client, proc *serverProc) {
		wav := sineWAV(48000, 1, framesForBytes(1*mib, 1), 440, 0.4)
		for _, id := range []string{"src_base_a", "src_base_b", "src_base_c"} {
			status, asset := c.putSource(sc, id, wav, 60*time.Second)
			c.expectStatus(sc, "register_"+id, status, 201)
			if status == 201 {
				getStatus, body := c.step(sc, "get_source:"+id, "GET", "/v1/sources/"+id, nil, 30*time.Second)
				c.expectStatus(sc, "read_back_"+id, getStatus, 200)
				var fetched domain.SourceAsset
				if err := json.Unmarshal(body, &fetched); err == nil && fetched.Digest != asset.Digest {
					sc.reason("read-back digest mismatch for %s", id)
				}
			}
		}
		spans := []domain.TimelineSpan{
			{SourceID: "src_base_a", SourceStartFrame: 0, SourceEndFrame: 19200, GainDB: -2},
			{SourceID: "src_base_b", SourceStartFrame: 0, SourceEndFrame: 16800, GainDB: 0, CrossfadeFrames: 4800},
		}
		status, _ := c.putTimeline(sc, "tl_base", 48000, 2, spans)
		c.expectStatus(sc, "compose_timeline", status, 201)
		facts := c.renderAndVerify(sc, "rnd_base", "tl_base", 60*time.Second, 30*time.Second)
		if facts.TerminalState != string(domain.RenderCompleted) {
			sc.reason("baseline render did not complete: %s", facts.TerminalState)
		}

		// Detail-read latency distribution on a quiet instance.
		for _, probe := range []struct {
			name string
			path string
		}{
			{"get_source", "/v1/sources/src_base_a"},
			{"get_timeline", "/v1/timelines/tl_base"},
			{"get_render", "/v1/renders/rnd_base"},
			{"get_receipt", "/v1/renders/rnd_base/receipt"},
		} {
			samples := make([]float64, 0, 20)
			for index := 0; index < 20; index++ {
				start := time.Now()
				outcome := c.doRaw("GET", probe.path, nil, 0, 30*time.Second)
				if outcome.status != 200 {
					sc.reason("latency probe %s returned %d", probe.name, outcome.status)
					break
				}
				samples = append(samples, float64(time.Since(start))/float64(time.Millisecond))
			}
			sc.rec.LatencyStats[probe.name] = latencyStats(samples)
		}
	})
}

func scenarioIngestMaxSource(env *runEnv, sc *scenario) {
	env.withServer("", func(c *client, proc *serverProc) {
		wav := sineWAV(48000, 2, framesForBytes(maxSourceBytes, 2), 440, 0.5)
		status, asset := c.putSource(sc, "src_max_ingest", wav, 120*time.Second)
		c.expectStatus(sc, "register_max_source", status, 201)
		if status == 201 {
			getStatus, body := c.step(sc, "get_source:src_max_ingest", "GET", "/v1/sources/src_max_ingest", nil, 30*time.Second)
			c.expectStatus(sc, "read_back", getStatus, 200)
			var fetched domain.SourceAsset
			if err := json.Unmarshal(body, &fetched); err == nil && fetched.Digest != asset.Digest {
				sc.reason("read-back digest mismatch")
			}
		}
	})
}

func scenarioMaxOutputSingleSource(env *runEnv, sc *scenario) {
	env.withServer("", func(c *client, proc *serverProc) {
		frames := framesForBytes(maxSourceBytes, 2)
		wav := sineWAV(48000, 2, frames, 440, 0.5)
		status, _ := c.putSource(sc, "src_max_out", wav, 120*time.Second)
		c.expectStatus(sc, "register_source", status, 201)
		status, plan := c.putTimeline(sc, "tl_max_out", 48000, 2, []domain.TimelineSpan{
			{SourceID: "src_max_out", SourceStartFrame: 0, SourceEndFrame: frames},
		})
		c.expectStatus(sc, "compose_timeline", status, 201)
		if status == 201 && plan.OutputFrames != frames {
			sc.reason("timeline output frames = %d, want %d", plan.OutputFrames, frames)
		}
		facts := c.renderAndVerify(sc, "rnd_max_out", "tl_max_out", 170*time.Second, 60*time.Second)
		if facts.TerminalState != string(domain.RenderCompleted) {
			sc.reason("max-output render did not complete: %s", facts.TerminalState)
		}
		sc.finding("single-source near-cap output: %d frames, %d output bytes", plan.OutputFrames, facts.OutputBytes)
	})
}

func scenarioMaxFramesSmallSources(env *runEnv, sc *scenario) {
	env.withServer("", func(c *client, proc *serverProc) {
		wav := sineWAV(48000, 1, framesForBytes(1*mib, 1), 440, 0.4)
		sourceFrames := framesForBytes(1*mib, 1)
		spans := make([]domain.TimelineSpan, 0, 16)
		for index := 0; index < 16; index++ {
			id := fmt.Sprintf("src_small_%02d", index)
			status, _ := c.putSource(sc, id, wav, 60*time.Second)
			c.expectStatus(sc, "register_"+id, status, 201)
			span := domain.TimelineSpan{SourceID: id, SourceStartFrame: 0, SourceEndFrame: sourceFrames}
			if index > 0 {
				span.CrossfadeFrames = 4800
			}
			spans = append(spans, span)
		}
		status, plan := c.putTimeline(sc, "tl_max_frames", 48000, 2, spans)
		c.expectStatus(sc, "compose_timeline", status, 201)
		if status == 201 && plan.OutputFrames > maxOutputFrames {
			sc.reason("timeline output frames %d exceed the cap", plan.OutputFrames)
		}
		facts := c.renderAndVerify(sc, "rnd_max_frames", "tl_max_frames", 170*time.Second, 60*time.Second)
		if facts.TerminalState != string(domain.RenderCompleted) {
			sc.reason("max-frames render did not complete: %s", facts.TerminalState)
		}
		sc.finding("16-source near-cap output: %d frames", plan.OutputFrames)
	})
}

func scenarioMaxSpans(env *runEnv, sc *scenario) {
	env.withServer("", func(c *client, proc *serverProc) {
		wav := sineWAV(48000, 1, framesForBytes(1*mib, 1), 440, 0.4)
		spans := make([]domain.TimelineSpan, 0, maxSpans)
		for index := 0; index < maxSpans; index++ {
			id := fmt.Sprintf("src_span_%02d", index)
			status, _ := c.putSource(sc, id, wav, 60*time.Second)
			c.expectStatus(sc, "register_"+id, status, 201)
			span := domain.TimelineSpan{SourceID: id, SourceStartFrame: 0, SourceEndFrame: 72000}
			if index > 0 {
				span.CrossfadeFrames = 4800
			}
			spans = append(spans, span)
		}
		status, _ := c.putTimeline(sc, "tl_max_spans", 48000, 2, spans)
		c.expectStatus(sc, "compose_timeline", status, 201)
		facts := c.renderAndVerify(sc, "rnd_max_spans", "tl_max_spans", 170*time.Second, 60*time.Second)
		if facts.TerminalState != string(domain.RenderCompleted) {
			sc.reason("max-spans render did not complete: %s", facts.TerminalState)
		}
	})
}

func scenarioTwoMaxSources(env *runEnv, sc *scenario) {
	env.withServer("", func(c *client, proc *serverProc) {
		frames := framesForBytes(maxSourceBytes, 2)
		wav := sineWAV(48000, 2, frames, 440, 0.5)
		for _, id := range []string{"src_dual_a", "src_dual_b"} {
			status, _ := c.putSource(sc, id, wav, 120*time.Second)
			c.expectStatus(sc, "register_"+id, status, 201)
		}
		spanLen := int64(4300000)
		spans := []domain.TimelineSpan{
			{SourceID: "src_dual_a", SourceStartFrame: 0, SourceEndFrame: spanLen},
			{SourceID: "src_dual_b", SourceStartFrame: 0, SourceEndFrame: spanLen, CrossfadeFrames: 4800},
		}
		status, plan := c.putTimeline(sc, "tl_dual_max", 48000, 2, spans)
		c.expectStatus(sc, "compose_timeline", status, 201)
		if status == 201 && plan.OutputFrames > maxOutputFrames {
			sc.reason("timeline output frames %d exceed the cap", plan.OutputFrames)
		}
		facts := c.renderAndVerify(sc, "rnd_dual_max", "tl_dual_max", 170*time.Second, 60*time.Second)
		if facts.TerminalState != string(domain.RenderCompleted) {
			sc.reason("two-source render did not complete: %s", facts.TerminalState)
		}
		sc.finding("two-source near-cap output: %d frames", plan.OutputFrames)
	})
}

func midSourceSpans(sc *scenario, c *client, timelineID string) {
	wav := sineWAV(48000, 1, framesForBytes(4*mib, 1), 440, 0.4)
	spans := make([]domain.TimelineSpan, 0, maxSpans)
	for index := 0; index < maxSpans; index++ {
		id := fmt.Sprintf("src_mid_%02d", index)
		status, _ := c.putSource(sc, id, wav, 120*time.Second)
		c.expectStatus(sc, "register_"+id, status, 201)
		spans = append(spans, domain.TimelineSpan{SourceID: id, SourceStartFrame: 0, SourceEndFrame: 36000})
	}
	status, _ := c.putTimeline(sc, timelineID, 48000, 2, spans)
	c.expectStatus(sc, "compose_timeline", status, 201)
}

func scenarioManyMidSourcesOverbudget(env *runEnv, sc *scenario) {
	env.withServer("", func(c *client, proc *serverProc) {
		midSourceSpans(sc, c, "tl_mid_over")
		sc.rec.Memory.PhaseHWMMb = map[string]float64{
			"after_uploads": float64(proc.hwmKB()) / 1024,
		}
		facts := c.renderAndVerify(sc, "rnd_mid_over", "tl_mid_over", 170*time.Second, 120*time.Second)
		if facts.TerminalState != string(domain.RenderCompleted) {
			sc.reason("over-budget render did not complete: %s", facts.TerminalState)
		}
		sc.finding("render completed unconstrained; peak RSS is the over-budget evidence")
	})
}

func scenarioManyMidSourcesCapped(env *runEnv, sc *scenario) {
	env.withServer("460MiB", func(c *client, proc *serverProc) {
		midSourceSpans(sc, c, "tl_mid_capped")
		sc.rec.Memory.PhaseHWMMb = map[string]float64{
			"after_uploads": float64(proc.hwmKB()) / 1024,
		}
		facts := c.renderAndVerify(sc, "rnd_mid_capped", "tl_mid_capped", 90*time.Second, 240*time.Second)
		// GOMEMLIMIT is a soft GC target, not a hard budget: the Go runtime may
		// still exceed it in RSS. The deployability verdict therefore comes from
		// the measured VmHWM, not from the limit being set.
		sc.finding("under GOMEMLIMIT=460MiB the render ended %q (job error %q); output GET status %d; VmHWM still reached the value recorded below",
			facts.TerminalState, facts.JobErrorCode, facts.OutputStatus)
	})
}

type trickleReader struct {
	inner   io.Reader
	rateBps float64
	started time.Time
	sent    int64
}

func (reader *trickleReader) Read(p []byte) (int, error) {
	n, err := reader.inner.Read(p)
	if n > 0 {
		reader.sent += int64(n)
		expected := time.Duration(float64(reader.sent) / reader.rateBps * float64(time.Second))
		if delay := time.Until(reader.started.Add(expected)); delay > 0 {
			time.Sleep(delay)
		}
	}
	return n, err
}

func scenarioSlowUploadTimeout(env *runEnv, sc *scenario) {
	env.withServer("", func(c *client, proc *serverProc) {
		payload := sineWAV(48000, 1, framesForBytes(30*mib, 1), 440, 0.4)
		body := mustJSON(service.SourceWriteRequest{
			Name:      "slow upload probe",
			WAVBase64: base64.StdEncoding.EncodeToString(payload),
		})
		trickle := &trickleReader{inner: bytes.NewReader(body), rateBps: 0.5 * mib, started: time.Now()}
		outcome := c.doRaw("PUT", "/v1/sources/src_slow", trickle, int64(len(body)), 120*time.Second)
		c.record(sc, "put_source_slow", "PUT", "/v1/sources/src_slow", int64(len(body)), outcome)

		// The server ReadTimeout (60s) truncates the body read; the handler then
		// maps the truncated JSON to 422 invalid_json instead of resetting the
		// connection. Either that or a client-side transport error proves the
		// combination undeliverable; the source must not become visible.
		timedOut := false
		switch {
		case outcome.clientErr != nil:
			timedOut = true
			sc.finding("server cut the 0.5 MiB/s upload after %s: %v", outcome.latency.Round(time.Second), outcome.clientErr)
		case outcome.status == 422 && outcome.latency >= 45*time.Second:
			timedOut = true
			sc.finding("server stopped reading at %s (ReadTimeout) and answered status %d code %q",
				outcome.latency.Round(time.Second), outcome.status, errorCodeOf(outcome.body))
		default:
			sc.reason("slow upload finished with status %d after %s; server ReadTimeout not observed", outcome.status, outcome.latency.Round(time.Second))
		}
		if timedOut {
			sc.reason("a 40 MiB request body at 0.5 MiB/s cannot be delivered within the 60s ReadTimeout")
			if outcome.latency < 45*time.Second || outcome.latency > 90*time.Second {
				sc.reason("upload cut after %s, outside the expected 45-90s ReadTimeout window", outcome.latency.Round(time.Second))
			}
		}

		// The failed upload must leave no visible source behind.
		status, _ := c.step(sc, "get_source:src_slow", "GET", "/v1/sources/src_slow", nil, 30*time.Second)
		if status != 404 {
			sc.reason("slow-uploaded source became visible with status %d", status)
		} else {
			sc.finding("rejected upload left no source: GET /v1/sources/src_slow = 404")
		}
	})
}

func scenarioConcurrentRegistrationsN(concurrency int) scenarioFunc {
	return func(env *runEnv, sc *scenario) {
		env.withServer("", func(c *client, proc *serverProc) {
			wav := sineWAV(48000, 2, framesForBytes(maxSourceBytes, 2), 440, 0.5)
			encoded := mustJSON(service.SourceWriteRequest{
				Name:      "concurrent probe",
				WAVBase64: base64.StdEncoding.EncodeToString(wav),
			})
			var wait sync.WaitGroup
			start := time.Now()
			for index := 0; index < concurrency; index++ {
				wait.Add(1)
				go func(index int) {
					defer wait.Done()
					id := fmt.Sprintf("src_conc_%d", index)
					outcome := c.doRaw("PUT", "/v1/sources/"+id, bytes.NewReader(encoded), int64(len(encoded)), 170*time.Second)
					c.record(sc, "put_source:"+id, "PUT", "/v1/sources/"+id, int64(len(encoded)), outcome)
					if outcome.status != 201 {
						sc.reason("concurrent registration %s returned %d", id, outcome.status)
					}
				}(index)
			}
			wait.Wait()
			sc.finding("%d concurrent max-size registrations finished in %s wall time", concurrency, time.Since(start).Round(time.Millisecond))
		})
	}
}

func scenarioWriteDuringRender(env *runEnv, sc *scenario) {
	env.withServer("", func(c *client, proc *serverProc) {
		frames := framesForBytes(16*mib, 2)
		wav := sineWAV(48000, 2, frames, 440, 0.5)
		for _, id := range []string{"src_busy_a", "src_busy_b"} {
			status, _ := c.putSource(sc, id, wav, 120*time.Second)
			c.expectStatus(sc, "register_"+id, status, 201)
		}
		spans := []domain.TimelineSpan{
			{SourceID: "src_busy_a", SourceStartFrame: 0, SourceEndFrame: frames},
			{SourceID: "src_busy_b", SourceStartFrame: 0, SourceEndFrame: frames, CrossfadeFrames: 4800},
		}
		status, _ := c.putTimeline(sc, "tl_busy", 48000, 2, spans)
		c.expectStatus(sc, "compose_timeline", status, 201)

		renderBody := mustJSON(service.RenderWriteRequest{TimelineID: "tl_busy"})
		renderDone := make(chan stepOutcome, 1)
		go func() {
			renderDone <- c.doRaw("PUT", "/v1/renders/rnd_busy", bytes.NewReader(renderBody), int64(len(renderBody)), 170*time.Second)
		}()
		time.Sleep(120 * time.Millisecond)

		// Probe a detail read while the render holds the service mutex.
		readOutcome := c.doRaw("GET", "/v1/sources/src_busy_a", nil, 0, 60*time.Second)
		c.record(sc, "get_source_during_render", "GET", "/v1/sources/src_busy_a", 0, readOutcome)
		if readOutcome.status != 200 {
			sc.reason("detail read during render returned %d", readOutcome.status)
		}

		// Probe render-job state visibility while rendering.
		jobOutcome := c.doRaw("GET", "/v1/renders/rnd_busy", nil, 0, 60*time.Second)
		jobState := ""
		if jobOutcome.status == 200 {
			var job domain.RenderJob
			if err := json.Unmarshal(jobOutcome.body, &job); err == nil {
				jobState = string(job.State)
			}
		}
		c.record(sc, "get_render_during_render", "GET", "/v1/renders/rnd_busy", 0, jobOutcome)
		sc.finding("job state observed mid-render: %q", jobState)

		// Probe a competing write; it must wait for the render to finish.
		small := sineWAV(48000, 1, framesForBytes(1*mib, 1), 440, 0.4)
		writeBody := mustJSON(service.SourceWriteRequest{
			Name:      "queued write probe",
			WAVBase64: base64.StdEncoding.EncodeToString(small),
		})
		writeOutcome := c.doRaw("PUT", "/v1/sources/src_busy_new", bytes.NewReader(writeBody), int64(len(writeBody)), 170*time.Second)
		c.record(sc, "put_source_during_render", "PUT", "/v1/sources/src_busy_new", int64(len(writeBody)), writeOutcome)
		if writeOutcome.status != 201 {
			sc.reason("queued write returned %d", writeOutcome.status)
		}

		renderOutcome := <-renderDone
		c.record(sc, "put_render:rnd_busy", "PUT", "/v1/renders/rnd_busy", int64(len(renderBody)), renderOutcome)
		if renderOutcome.status != 201 {
			sc.reason("busy render returned %d", renderOutcome.status)
		}
		facts := c.verifyRender(sc, "rnd_busy", 60*time.Second)
		if facts.TerminalState != string(domain.RenderCompleted) {
			sc.reason("busy render terminal state = %s", facts.TerminalState)
		}
	})
}

func scenarioConcurrentDownloads(env *runEnv, sc *scenario) {
	started := time.Now()
	// Phase A: produce a completed 32 MiB render on a first server instance.
	procA, err := startServer(env.binary, "")
	if err != nil {
		sc.reason("server A start failed: %v", err)
		return
	}
	dataDir := procA.dataDir
	defer func() {
		sc.rec.WallMS = float64(time.Since(started)) / float64(time.Millisecond)
	}()
	clientA := newClient(procA.baseURL)
	frames := framesForBytes(maxSourceBytes, 2)
	wav := sineWAV(48000, 2, frames, 440, 0.5)
	status, _ := clientA.putSource(sc, "src_dl", wav, 120*time.Second)
	clientA.expectStatus(sc, "register_source", status, 201)
	status, _ = clientA.putTimeline(sc, "tl_dl", 48000, 2, []domain.TimelineSpan{
		{SourceID: "src_dl", SourceStartFrame: 0, SourceEndFrame: frames},
	})
	clientA.expectStatus(sc, "compose_timeline", status, 201)
	facts := clientA.renderAndVerify(sc, "rnd_dl", "tl_dl", 170*time.Second, 60*time.Second)
	if facts.TerminalState != string(domain.RenderCompleted) {
		sc.reason("download-setup render did not complete: %s", facts.TerminalState)
		procA.Shutdown()
		procA.RemoveData()
		return
	}
	hwmA := float64(procA.hwmKB()) / 1024
	procA.Shutdown()

	// Phase B: a fresh server instance on the same data dir serves only the
	// concurrent downloads, so its VmHWM isolates the download path.
	procB, err := startServerOnDir(env.binary, "", dataDir)
	if err != nil {
		sc.reason("server B start failed: %v", err)
		procA.RemoveData()
		return
	}
	defer func() {
		hwmB := float64(procB.hwmKB()) / 1024
		sc.rec.Memory.IdleRSSMB = float64(procB.currentRSSkB()) / 1024
		sc.rec.Memory.PeakRSSMB = float64(procB.peakPolledkB()) / 1024
		sc.rec.Memory.VmHWMMb = math.Max(hwmA, hwmB)
		sc.rec.Memory.PhaseHWMMb = map[string]float64{
			"render_server":   hwmA,
			"download_server": hwmB,
		}
		procB.Shutdown()
		procB.RemoveData()
	}()
	clientB := newClient(procB.baseURL)
	var wait sync.WaitGroup
	for index := 0; index < 4; index++ {
		wait.Add(1)
		go func(index int) {
			defer wait.Done()
			outcome := clientB.doRaw("GET", "/v1/renders/rnd_dl/output", nil, 0, 120*time.Second)
			clientB.record(sc, fmt.Sprintf("get_output_concurrent_%d", index), "GET", "/v1/renders/rnd_dl/output", 0, outcome)
			if outcome.status == 200 {
				sum := sha256.Sum256(outcome.body)
				if hex.EncodeToString(sum[:]) != facts.ReceiptDigest {
					sc.reason("concurrent download %d digest mismatch", index)
				}
			} else {
				sc.reason("concurrent download %d returned %d", index, outcome.status)
			}
		}(index)
	}
	wait.Wait()
}

// scenarioCrashMidRender kills the server with SIGKILL while a large render is
// in flight (simulating a hard memory-enforcement event such as a cgroup OOM
// kill), then restarts a fresh server on the same data directory and records
// what an operator can actually observe: the durable job record, the output
// and receipt routes, and whether the wedged render id can be re-driven.
func scenarioCrashMidRender(env *runEnv, sc *scenario) {
	started := time.Now()
	procA, err := startServer(env.binary, "")
	if err != nil {
		sc.reason("server A start failed: %v", err)
		return
	}
	dataDir := procA.dataDir
	defer func() {
		sc.rec.WallMS = float64(time.Since(started)) / float64(time.Millisecond)
	}()
	clientA := newClient(procA.baseURL)
	frames := framesForBytes(maxSourceBytes, 2)
	wav := sineWAV(48000, 2, frames, 440, 0.5)
	for _, id := range []string{"src_crash_a", "src_crash_b"} {
		status, _ := clientA.putSource(sc, id, wav, 120*time.Second)
		clientA.expectStatus(sc, "register_"+id, status, 201)
	}
	spanLen := int64(4300000)
	status, _ := clientA.putTimeline(sc, "tl_crash", 48000, 2, []domain.TimelineSpan{
		{SourceID: "src_crash_a", SourceStartFrame: 0, SourceEndFrame: spanLen},
		{SourceID: "src_crash_b", SourceStartFrame: 0, SourceEndFrame: spanLen, CrossfadeFrames: 4800},
	})
	clientA.expectStatus(sc, "compose_timeline", status, 201)

	renderBody := mustJSON(service.RenderWriteRequest{TimelineID: "tl_crash"})
	renderDone := make(chan stepOutcome, 1)
	go func() {
		renderDone <- clientA.doRaw("PUT", "/v1/renders/rnd_crash", bytes.NewReader(renderBody), int64(len(renderBody)), 170*time.Second)
	}()
	time.Sleep(120 * time.Millisecond)
	hwmA := float64(procA.hwmKB()) / 1024
	procA.Kill()
	renderOutcome := <-renderDone
	clientA.record(sc, "put_render:rnd_crash", "PUT", "/v1/renders/rnd_crash", int64(len(renderBody)), renderOutcome)
	if renderOutcome.clientErr == nil {
		sc.finding("render PUT returned status %d despite the kill (render may have finished before SIGKILL)", renderOutcome.status)
	} else {
		sc.finding("render PUT observed the kill as: %v", renderOutcome.clientErr)
	}

	// Phase B: restart on the same data directory and inspect the wreckage.
	procB, err := startServerOnDir(env.binary, "", dataDir)
	if err != nil {
		sc.reason("server B start failed: %v", err)
		procA.RemoveData()
		return
	}
	defer func() {
		hwmB := float64(procB.hwmKB()) / 1024
		sc.rec.Memory.VmHWMMb = math.Max(hwmA, hwmB)
		sc.rec.Memory.PhaseHWMMb = map[string]float64{
			"killed_server":    hwmA,
			"restarted_server": hwmB,
		}
		procB.Shutdown()
		procB.RemoveData()
	}()
	clientB := newClient(procB.baseURL)

	status, body := clientB.step(sc, "get_render:rnd_crash", "GET", "/v1/renders/rnd_crash", nil, 30*time.Second)
	wedgedState := ""
	if status == 200 {
		var job domain.RenderJob
		if err := json.Unmarshal(body, &job); err == nil {
			wedgedState = string(job.State)
		}
	}
	sc.finding("after SIGKILL + restart the render job reads back as state %q", wedgedState)
	if wedgedState == string(domain.RenderCompleted) || wedgedState == string(domain.RenderFailed) {
		sc.reason("killed render unexpectedly reached terminal state %q; stale-job gap not demonstrated", wedgedState)
	}
	if wedgedState != "" && wedgedState != string(domain.RenderCompleted) && wedgedState != string(domain.RenderFailed) {
		sc.reason("hard kill leaves the render job in non-terminal state %q with no automatic recovery", wedgedState)
	}

	rStatus, _ := clientB.step(sc, "get_receipt:rnd_crash", "GET", "/v1/renders/rnd_crash/receipt", nil, 30*time.Second)
	oStatus, oBody := clientB.step(sc, "get_output:rnd_crash", "GET", "/v1/renders/rnd_crash/output", nil, 30*time.Second)
	sc.finding("receipt GET = %d, output GET = %d code %q", rStatus, oStatus, errorCodeOf(oBody))
	if oStatus == 200 {
		sc.reason("partial output became downloadable after the kill")
	}

	// The idempotent re-PUT of the same render id returns the stale record
	// instead of re-driving the render: the id stays wedged.
	reStatus, reBody := clientB.step(sc, "put_render_replay:rnd_crash", "PUT", "/v1/renders/rnd_crash", service.RenderWriteRequest{TimelineID: "tl_crash"}, 30*time.Second)
	replayState := ""
	if reStatus == 200 || reStatus == 201 {
		var job domain.RenderJob
		if err := json.Unmarshal(reBody, &job); err == nil {
			replayState = string(job.State)
		}
	}
	sc.finding("idempotent replay of the wedged render id returned status %d with state %q", reStatus, replayState)
	if replayState != "" && replayState != string(domain.RenderCompleted) {
		sc.reason("render id rnd_crash is wedged in state %q; idempotent replay cannot re-drive it", replayState)
	}

	// A new render id on the same timeline must still succeed: the service
	// recovers, only the wedged id is affected.
	facts := clientB.renderAndVerify(sc, "rnd_crash_recovery", "tl_crash", 170*time.Second, 60*time.Second)
	if facts.TerminalState != string(domain.RenderCompleted) {
		sc.reason("recovery render on a fresh id did not complete: %s", facts.TerminalState)
	} else {
		sc.finding("a fresh render id on the same timeline completed and downloaded correctly")
	}
}

// ---------- stats ----------

func latencyStats(samples []float64) LatencyStat {
	if len(samples) == 0 {
		return LatencyStat{}
	}
	sorted := append([]float64(nil), samples...)
	sort.Float64s(sorted)
	sum := 0.0
	for _, value := range sorted {
		sum += value
	}
	pick := func(q float64) float64 {
		index := int(math.Ceil(q*float64(len(sorted)))) - 1
		if index < 0 {
			index = 0
		}
		return sorted[index]
	}
	return LatencyStat{
		N:      len(sorted),
		MinMS:  sorted[0],
		P50MS:  pick(0.50),
		P95MS:  pick(0.95),
		MaxMS:  sorted[len(sorted)-1],
		MeanMS: sum / float64(len(sorted)),
	}
}

// ---------- main ----------

var scenarioRegistry = []struct {
	id      string
	purpose string
	limits  map[string]any
	expect  string
	fn      scenarioFunc
}{
	{
		id:      "limits-enforcement",
		purpose: "Confirm each configured limit individually rejects overflow with a stable error code.",
		limits: map[string]any{
			"source_bytes_exact":    maxSourceBytes,
			"source_bytes_over":     "32 MiB + 1 frame",
			"request_bytes_over":    "37 MiB payload (~49.4 MiB body)",
			"spans_over":            maxSpans + 1,
			"output_frames_over":    maxOutputFrames + 1,
			"server_read_timeout_s": 60,
		},
		expect: "commit (all five limit rejections observed with stable codes)",
		fn:     scenarioLimitsEnforcement,
	},
	{
		id:      "baseline-ordinary",
		purpose: "Ordinary register/compose/render/read mix with detail-read latency distribution.",
		limits:  map[string]any{"source_bytes_each": 1 * mib, "sources": 3, "spans": 2, "output_frames": 31200},
		expect:  "commit",
		fn:      scenarioBaselineOrdinary,
	},
	{
		id:      "ingest-max-source",
		purpose: "Register the largest legal source (32 MiB) and read it back.",
		limits:  map[string]any{"source_bytes": maxSourceBytes, "request_bytes": "~44.7 MiB"},
		expect:  "commit",
		fn:      scenarioIngestMaxSource,
	},
	{
		id:      "render-max-output-single-source",
		purpose: "One 32 MiB stereo source rendered to a near-cap single-span output (legal near-limit production path).",
		limits:  map[string]any{"source_bytes": maxSourceBytes, "spans": 1, "output_frames": framesForBytes(maxSourceBytes, 2)},
		expect:  "commit or boundary",
		fn:      scenarioMaxOutputSingleSource,
	},
	{
		id:      "render-max-frames-small-sources",
		purpose: "Sixteen 1 MiB sources composed to a near-cap output frame count (legal near-limit production path).",
		limits:  map[string]any{"source_bytes_each": 1 * mib, "sources": 16, "spans": 16, "output_frames": 8316256},
		expect:  "commit or boundary",
		fn:      scenarioMaxFramesSmallSources,
	},
	{
		id:      "render-max-spans",
		purpose: "Timeline at the 64-span cap with 64 small distinct sources.",
		limits:  map[string]any{"source_bytes_each": 1 * mib, "sources": 64, "spans": maxSpans, "output_frames": 4305600},
		expect:  "commit or boundary",
		fn:      scenarioMaxSpans,
	},
	{
		id:      "render-two-max-sources",
		purpose: "Two 32 MiB sources rendered to a near-cap output; probes the combined source+output envelope.",
		limits:  map[string]any{"source_bytes_each": maxSourceBytes, "sources": 2, "spans": 2, "output_frames": 8595200},
		expect:  "boundary or gap",
		fn:      scenarioTwoMaxSources,
	},
	{
		id:      "render-many-mid-sources-overbudget",
		purpose: "64 spans over 64 distinct 4 MiB sources (256 MiB of registered media); predicted to exceed the 512 MiB budget.",
		limits:  map[string]any{"source_bytes_each": 4 * mib, "sources": 64, "spans": maxSpans, "output_frames": 2304000},
		expect:  "gap (peak RSS over budget)",
		fn:      scenarioManyMidSourcesOverbudget,
	},
	{
		id:      "render-many-mid-sources-capped",
		purpose: "Same combination under GOMEMLIMIT=460MiB to capture the enforced-budget failure signature.",
		limits:  map[string]any{"source_bytes_each": 4 * mib, "sources": 64, "spans": maxSpans, "output_frames": 2304000},
		expect:  "gap (job fails or client times out; output stays unavailable)",
		fn:      scenarioManyMidSourcesCapped,
	},
	{
		id:      "slow-upload-read-timeout",
		purpose: "A 40 MiB request body trickled at 0.5 MiB/s must be cut by the server ReadTimeout (60s).",
		limits:  map[string]any{"request_bytes": "~40 MiB", "upload_rate": "0.5 MiB/s", "server_read_timeout_s": 60},
		expect:  "gap (client observes server-side timeout)",
		fn:      scenarioSlowUploadTimeout,
	},
	{
		id:      "concurrent-max-registrations-2",
		purpose: "Two concurrent 32 MiB registrations; probes HTTP-layer memory multiplication at low concurrency.",
		limits:  map[string]any{"source_bytes_each": maxSourceBytes, "concurrency": 2},
		expect:  "commit or boundary",
		fn:      scenarioConcurrentRegistrationsN(2),
	},
	{
		id:      "concurrent-max-registrations-3",
		purpose: "Three concurrent 32 MiB registrations; probes the concurrency commit boundary.",
		limits:  map[string]any{"source_bytes_each": maxSourceBytes, "concurrency": 3},
		expect:  "commit or boundary",
		fn:      scenarioConcurrentRegistrationsN(3),
	},
	{
		id:      "concurrent-max-registrations-4",
		purpose: "Four concurrent 32 MiB registrations; predicted to exceed the 512 MiB budget.",
		limits:  map[string]any{"source_bytes_each": maxSourceBytes, "concurrency": 4},
		expect:  "gap (peak RSS over budget)",
		fn:      scenarioConcurrentRegistrationsN(4),
	},
	{
		id:      "write-during-render",
		purpose: "Detail reads and a competing write probed while a large render holds the service mutex.",
		limits:  map[string]any{"source_bytes_each": 16 * mib, "sources": 2, "output_frames": 8383786},
		expect:  "commit or boundary (reads stay fast, writes queue behind the render)",
		fn:      scenarioWriteDuringRender,
	},
	{
		id:      "concurrent-output-downloads",
		purpose: "Four concurrent downloads of a 32 MiB render output served by a fresh instance; isolates read-path memory multiplication.",
		limits:  map[string]any{"output_bytes": 33554432, "concurrency": 4},
		expect:  "commit or boundary",
		fn:      scenarioConcurrentDownloads,
	},
	{
		id:      "crash-mid-render-stale-job",
		purpose: "SIGKILL the server mid-render (hard enforcement proxy), restart on the same data dir, and record the observable wreckage.",
		limits:  map[string]any{"source_bytes_each": maxSourceBytes, "sources": 2, "kill": "SIGKILL at +120ms of render"},
		expect:  "gap (stale non-terminal job; output unavailable; render id wedged)",
		fn:      scenarioCrashMidRender,
	},
}

func main() {
	outPath := flag.String("out", "capacity-evidence.json", "evidence JSON output path")
	only := flag.String("only", "", "comma-separated scenario IDs to run (default: all)")
	repoDir := flag.String("repo", ".", "repository root used to build the server")
	flag.Parse()

	repoAbs, err := filepath.Abs(*repoDir)
	if err != nil {
		fmt.Fprintln(os.Stderr, "resolve repo:", err)
		os.Exit(1)
	}
	tempRoot, err := os.MkdirTemp("", "capacity-check-*")
	if err != nil {
		fmt.Fprintln(os.Stderr, "temp dir:", err)
		os.Exit(1)
	}
	defer os.RemoveAll(tempRoot)

	binary := filepath.Join(tempRoot, "voiceservice")
	build := exec.Command("go", "build", "-o", binary, "./cmd/voiceservice")
	build.Dir = repoAbs
	build.Env = os.Environ()
	if output, err := build.CombinedOutput(); err != nil {
		fmt.Fprintln(os.Stderr, "build server:", err, string(output))
		os.Exit(1)
	}
	binaryBytes, err := os.ReadFile(binary)
	if err != nil {
		fmt.Fprintln(os.Stderr, "read binary:", err)
		os.Exit(1)
	}
	binaryHash := sha256.Sum256(binaryBytes)

	gitHead := ""
	if rev, err := exec.Command("git", "-C", repoAbs, "rev-parse", "HEAD").Output(); err == nil {
		gitHead = strings.TrimSpace(string(rev))
	}

	evidence := Evidence{
		Tool:      "capacitycheck (cmd/capacitycheck)",
		StartedAt: time.Now().UTC().Format(time.RFC3339),
		Host: map[string]any{
			"goos":         runtime.GOOS,
			"goarch":       runtime.GOARCH,
			"cpus":         runtime.NumCPU(),
			"go_version":   runtime.Version(),
			"mem_total_mb": hostMemTotalMB(),
		},
		ServerBinary:     "cmd/voiceservice built with production defaults (no source changes)",
		ServerSHA256:     hex.EncodeToString(binaryHash[:]),
		GitHead:          gitHead,
		BudgetMiB:        budgetMiB,
		CommitCeilingMiB: commitCeilingMiB,
	}

	selected := map[string]bool{}
	if *only != "" {
		for _, id := range strings.Split(*only, ",") {
			selected[strings.TrimSpace(id)] = true
		}
	}

	for _, entry := range scenarioRegistry {
		if len(selected) > 0 && !selected[entry.id] {
			continue
		}
		sc := newScenario(entry.id, entry.purpose, entry.limits, entry.expect)
		env := &runEnv{binary: binary, scenario: sc}
		fmt.Printf("== scenario %s ...\n", entry.id)
		entry.fn(env, sc)
		sc.finalize()
		evidence.Scenarios = append(evidence.Scenarios, sc.rec)
		fmt.Printf("   verdict=%s vmhwm=%.1fMiB wall=%.0fms reasons=%v\n",
			sc.rec.Verdict, sc.rec.Memory.VmHWMMb, sc.rec.WallMS, sc.rec.VerdictReasons)
	}

	encoded, err := json.MarshalIndent(evidence, "", "  ")
	if err != nil {
		fmt.Fprintln(os.Stderr, "marshal evidence:", err)
		os.Exit(1)
	}
	if dir := filepath.Dir(*outPath); dir != "." {
		if err := os.MkdirAll(dir, 0o755); err != nil {
			fmt.Fprintln(os.Stderr, "create evidence dir:", err)
			os.Exit(1)
		}
	}
	if err := os.WriteFile(*outPath, encoded, 0o644); err != nil {
		fmt.Fprintln(os.Stderr, "write evidence:", err)
		os.Exit(1)
	}
	fmt.Println("evidence written to", *outPath)
}

func hostMemTotalMB() int64 {
	data, err := os.ReadFile("/proc/meminfo")
	if err != nil {
		return 0
	}
	for _, line := range strings.Split(string(data), "\n") {
		fields := strings.Fields(line)
		if len(fields) == 3 && fields[0] == "MemTotal:" {
			value, err := strconv.ParseInt(fields[1], 10, 64)
			if err == nil {
				return value / 1024
			}
		}
	}
	return 0
}
