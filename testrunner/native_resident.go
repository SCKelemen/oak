package testrunner

import (
	"encoding/binary"
	"io"
	"os/exec"
	"sync"
	"time"
)

// A residentWorker is one harness process in serve mode (nativeServe): it
// takes case records on its stdin and answers on its stdout, running each
// case in a fresh fork. A worker is used by one case at a time.
type residentWorker struct {
	cmd    *exec.Cmd
	stdin  io.WriteCloser
	stdout io.ReadCloser
	once   sync.Once
}

// kill ends the worker and any fork it has running: the workers run in
// their own process group so a timed-out case cannot outlive its worker.
func (w *residentWorker) kill() {
	w.once.Do(func() {
		killProcessGroup(w.cmd)
		_ = w.stdin.Close()
		_ = w.stdout.Close()
		_ = w.cmd.Wait()
	})
}

// acquireWorker takes an idle worker or starts one. The runner's case
// goroutines call run concurrently, so the pool grows to their number and
// no further.
func (p *nativeProgram) acquireWorker() (*residentWorker, error) {
	p.mu.Lock()
	if n := len(p.idle); n > 0 {
		w := p.idle[n-1]
		p.idle = p.idle[:n-1]
		p.mu.Unlock()
		return w, nil
	}
	p.mu.Unlock()
	cmd := exec.Command(p.bin, "serve")
	cmd.SysProcAttr = processGroupAttr()
	cmd.Stderr = io.Discard
	stdin, err := cmd.StdinPipe()
	if err != nil {
		return nil, err
	}
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		return nil, err
	}
	if err := cmd.Start(); err != nil {
		return nil, err
	}
	w := &residentWorker{cmd: cmd, stdin: stdin, stdout: stdout}
	p.mu.Lock()
	p.workers[w] = true
	p.mu.Unlock()
	return w, nil
}

func (p *nativeProgram) releaseWorker(w *residentWorker) {
	p.mu.Lock()
	p.idle = append(p.idle, w)
	p.mu.Unlock()
}

func (p *nativeProgram) discardWorker(w *residentWorker) {
	p.mu.Lock()
	delete(p.workers, w)
	p.mu.Unlock()
	w.kill()
}

// close ends every worker; the runner calls it before removing the build
// directory.
func (p *nativeProgram) close() {
	p.mu.Lock()
	workers := make([]*residentWorker, 0, len(p.workers))
	for w := range p.workers {
		workers = append(workers, w)
	}
	p.workers = map[*residentWorker]bool{}
	p.idle = nil
	p.mu.Unlock()
	for _, w := range workers {
		w.kill()
	}
}

// runResident runs one case through a worker: the record on its stdin, the
// wait status and the child's output in the reply. The case timeout kills
// the worker's process group, so the reply fails and the case is a
// timeout, exactly as a killed per-case process is.
func (p *nativeProgram) runResident(index int, input []byte, reportPath string) (status exitStatus, output string, timedOut bool) {
	w, err := p.acquireWorker()
	if err != nil {
		return exitStatus{err: err}, "", false
	}
	record := make([]byte, 12, 12+len(reportPath)+len(input))
	binary.LittleEndian.PutUint32(record[0:], uint32(index))
	binary.LittleEndian.PutUint32(record[4:], uint32(len(reportPath)))
	binary.LittleEndian.PutUint32(record[8:], uint32(len(input)))
	record = append(append(record, reportPath...), input...)
	watchdog := time.AfterFunc(p.timeout, w.kill)
	var reply [16]byte
	var out []byte
	if _, err = w.stdin.Write(record); err == nil {
		if _, err = io.ReadFull(w.stdout, reply[:]); err == nil {
			if length := binary.LittleEndian.Uint32(reply[8:]); length <= outputLimit {
				out = make([]byte, length)
				_, err = io.ReadFull(w.stdout, out)
			} else {
				err = io.ErrUnexpectedEOF
			}
		}
	}
	if !watchdog.Stop() {
		// The watchdog fired: the worker and its fork are gone.
		p.discardWorker(w)
		return exitStatus{err: err}, string(out), true
	}
	if err != nil {
		p.discardWorker(w)
		return exitStatus{err: err}, string(out), false
	}
	p.releaseWorker(w)
	flags := binary.LittleEndian.Uint32(reply[12:])
	output = string(out)
	if flags&1 != 0 {
		output += "\n[output truncated]"
	}
	value := int(binary.LittleEndian.Uint32(reply[4:]))
	if binary.LittleEndian.Uint32(reply[0:]) == 1 {
		return exitStatus{ran: true, signal: signalNumber(value), core: flags&2 != 0}, output, false
	}
	return exitStatus{ran: true, exited: true, code: value}, output, false
}
