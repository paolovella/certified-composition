#!/usr/bin/env python3
"""AI-01 step 1: which files rely on autoImplicit, measured without changing anything.

Each file runs in its own process group, killed as a group on timeout or above 12 GB resident. A timeout or a kill is
NO VERDICT, never zero errors. Usage, from the repo root: python3 research/2026-11/autoimplicit_measure.py
"""
import os, re, signal, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor

TIMEOUT = 1800
CAP_KB = 12 * 2 ** 20
ERR = re.compile(r'^\S+\.lean:\d+:\d+: error')


def rss(pgid):
    r = subprocess.run(['ps', '-o', 'rss=', '-g', str(pgid)], capture_output=True, text=True)
    return sum(int(x) for x in r.stdout.split())


def check(job):
    pkg, f = job
    with tempfile.TemporaryFile('w+') as log:
        p = subprocess.Popen(['lake', 'env', 'lean', '-D', 'autoImplicit=false', f], cwd=pkg, stdout=log, stderr=subprocess.STDOUT,
                             text=True, start_new_session=True)
        t0 = time.time()
        while p.poll() is None:
            time.sleep(1)
            if time.time() - t0 > TIMEOUT or rss(p.pid) > CAP_KB:
                os.killpg(p.pid, signal.SIGKILL)
                p.wait()
                return pkg, f, None, 0
        log.seek(0)
        errs = sum(1 for l in log if ERR.match(l))
        return pkg, f, errs, p.returncode


jobs = []
for pkg in ['conf-typing', 'transport-calculus', 'transport-kernel']:
    for root, dirs, files in os.walk(pkg):
        dirs[:] = [d for d in dirs if d != '.lake']
        for n in files:
            if n.endswith('.lean') and not n.startswith('lakefile'):
                jobs.append((pkg, os.path.relpath(os.path.join(root, n), pkg)))

bad = 0
with ThreadPoolExecutor(3) as ex:
    for pkg, f, errs, rc in ex.map(check, jobs):
        if errs is None:
            print('NO VERDICT', pkg, f, flush=True)
            bad += 1
        elif errs:
            print(errs, pkg, f, flush=True)
        elif rc != 0:
            # A nonzero exit with no error line is not "this file is clean".
            print('NO VERDICT', pkg, f, 'exit', rc, flush=True)
            bad += 1
print('files', len(jobs), 'no verdict', bad)
sys.exit(1 if bad else 0)
