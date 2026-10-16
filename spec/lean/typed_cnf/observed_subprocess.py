"""Observe fixed preflight calls while retaining Python's run control flow.

Adapted from the pinned Python 3.12 subprocess.run implementation. Popen,
communicate, kill, wait, poll and context exit retain their original ordering;
the only additions are observational hooks and the outer finally hook.
"""
import subprocess


def run(owner, role, *popenargs, input=None, capture_output=False,
        timeout=None, check=False, **kwargs):
    if input is not None:
        if kwargs.get('stdin') is not None:
            raise ValueError('stdin and input arguments may not both be used.')
        kwargs['stdin'] = subprocess.PIPE
    if capture_output:
        if kwargs.get('stdout') is not None or kwargs.get('stderr') is not None:
            raise ValueError('stdout and stderr arguments may not be used with capture_output.')
        kwargs['stdout'] = subprocess.PIPE
        kwargs['stderr'] = subprocess.PIPE
    process = None
    try:
        with subprocess.Popen(*popenargs, **kwargs) as process:
            try:
                owner.observe('spawned', owner, process.pid, role)
                stdout, stderr = process.communicate(input, timeout=timeout)
            except subprocess.TimeoutExpired as exc:
                process.kill()
                if subprocess._mswindows:
                    exc.stdout, exc.stderr = process.communicate()
                else:
                    process.wait()
                raise
            except:
                process.kill()
                # Popen.__exit__ performs the original wait on this path.
                raise
            retcode = process.poll()
            if check and retcode:
                raise subprocess.CalledProcessError(retcode, process.args,
                                                    output=stdout, stderr=stderr)
        return subprocess.CompletedProcess(process.args, retcode, stdout, stderr)
    finally:
        # Context exit has already completed. Never infer a raw wait4 status.
        if process is not None and process.returncode is not None:
            owner.observe('joined_decoded', process.pid, process.returncode, role)
