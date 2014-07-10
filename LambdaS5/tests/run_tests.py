#!/usr/bin/env python

import os
import sys
import glob
import tempfile
import itertools
import subprocess

# Hack to work with Python 2 and 3.
if sys.version_info[0] >= 3:
    from io import BytesIO
    imap = map
else:
    from cStringIO import StringIO as BytesIO
    imap = itertools.imap

if len(sys.argv) == 2:
    ES5_ENV = sys.argv[1]
elif len(sys.argv) == 1:
    ES5_ENV = None
else:
    print('Syntax: %s <env dump>' % sys.argv[0])
    exit(2)

TEST_DIR = os.path.dirname(__file__)
EXE = os.path.join(TEST_DIR, '..', 'build', 'eval.native')

def strip_extension(filename):
    return filename[0:-len('.in.ljs')]
def list_ljs(dirname):
    return glob.glob(os.path.join(TEST_DIR, dirname, '*.in.ljs'))
def list_tests(dirname):
    return imap(strip_extension, list_ljs(dirname))

tests = imap(lambda x:(None, x), list_tests('no-env'))

if ES5_ENV:
    tests = itertools.chain(tests,
        imap(lambda x:(ES5_ENV, x), list_tests('with-env')))


successes = []
fails = []
skipped = []
for (env, test) in tests:
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
    if env:
        command = [EXE, '-load', env]
    else:
        command = [EXE]
    with open(in_) as in_fd:
        try:
            output = subprocess.check_output(command + ['stdin'], stdin=in_fd)
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
