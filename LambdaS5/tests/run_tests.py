#!/usr/bin/env python

import os
import sys
import glob
import tempfile
import subprocess

# Hack to work with Python 2 and 3.
if sys.version_info[0] >= 3:
    from io import BytesIO
else:
    from cStringIO import StringIO as BytesIO

TEST_DIR = os.path.dirname(__file__)
EXE = os.path.join(TEST_DIR, '..', 'build', 'eval.native')


successes = []
fails = []
skipped = []
for test in map(lambda x:x[0:-len('.in.ljs')],
                glob.glob(os.path.join(TEST_DIR, '*.in.ljs'))):
    in_ = test + '.in.ljs'
    out = test + '.out.ljs'
    skip = test + '.skip'
    sys.stdout.write('%s... ' % test)
    sys.stdout.flush()
    if os.path.isfile(skip):
        with open(skip) as fd:
            skipped.append((test, fd.read()))
        print('skipped.')
        continue
    with open(in_) as in_fd:
        try:
            output = subprocess.check_output([EXE, 'stdin'], stdin=in_fd)
        except subprocess.CalledProcessError:
            fails.append(test)
            continue
    with tempfile.TemporaryFile() as out_fd:
        out_fd.write(output)
        out_fd.seek(0)
        if subprocess.call(['diff', '-', out], stdin=out_fd):
            fails.append(test)
        else:
            successes.append(test)
            print('ok.')

print('Result:')
print('\t%d successed' % len(successes))
print('\t%d skipped:' % len(skipped))
for (test, msg) in skipped:
    print('\t\t%s: %s' % (test, msg))
print('\t%d failed:' % len(fails))
for fail in fails:
    print('\t\t%s' % fail)
if fails:
   exit(1)
else:
    exit(0)
