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

LJS_BIN = None
if len(sys.argv) == 4:
    (prog, ES5_ENV, LJS_BIN, ljs_tests_dir) = sys.argv
    ljs_tests = glob.glob(os.path.join(ljs_tests_dir, '*.js'))
elif len(sys.argv) == 2:
    ES5_ENV = sys.argv[1]
elif len(sys.argv) == 1:
    ES5_ENV = None
else:
    prog = sys.argv[0]
    print('Syntax: (any of the following)')
    print('\t%s' % prog)
    print('\t%s <env dump>' % prog)
    print('\t%s <env dump> <lambdajs bin> <lambdajs tests dir>' % sys.argv[0])
    exit(2)

TEST_DIR = os.path.dirname(__file__)
EXE = os.path.join(TEST_DIR, '..', 'build', 'eval.native')

def strip_extension(filename):
    return filename[0:-len('.in.ljs')]
def list_ljs(dirname):
    return glob.glob(os.path.join(TEST_DIR, dirname, '*.in.ljs'))
def list_tests(dirname):
    return imap(strip_extension, list_ljs(dirname))

tests = imap(lambda x:(None, None, x), list_tests('no-env'))

if ES5_ENV:
    tests = itertools.chain(tests,
        imap(lambda x:(ES5_ENV, None, x), list_tests('with-env')))
if LJS_BIN:
    tests = itertools.chain(tests,
        imap(lambda x:(ES5_ENV, LJS_BIN, x), ljs_tests ))


successes = []
fails = []
skipped = []
def run_test(env, ljs_bin, test):
    global successes, fails, skipped
    in_ = test + '.in.ljs'
    out = test + '.out.ljs'
    skip = test + '.skip'
    sys.stdout.write('%s... ' % test)
    sys.stdout.flush()
    if os.path.isfile(skip):
        with open(skip) as fd:
            skipped.append((test, fd.read()))
        print('skipped.')
        return
    if env:
        command = [EXE, '-load', env]
    else:
        command = [EXE]
    if ljs_bin:
        if 'eval' in test.rsplit('/', 1)[-1].split('.', 1)[0].split('-'):
            skipped.append((test, 'Requires eval'))
            print('skipped')
            return
        with tempfile.TemporaryFile() as desugared:
            subprocess.call([ljs_bin, '-desugar', test, '-print-src'], stdout=desugared)
            desugared.seek(0)
            output = subprocess.check_output(command + ['stdin'], stdin=desugared)
        if 'passed' in output or 'Passed' in output:
            successes.append(test)
            print('ok.')
        else:
            print(output)
            fails.append(test)
        del desugared
    else:
        with open(in_) as in_fd:
            try:
                    output = subprocess.check_output(command + ['stdin'], stdin=in_fd)
            except subprocess.CalledProcessError:
                fails.append(test)
                return
        with tempfile.TemporaryFile() as out_fd:
            out_fd.write(output)
            out_fd.seek(0)
            if subprocess.call(['diff', '-', out], stdin=out_fd):
                fails.append(test)
            else:
                successes.append(test)
                print('ok.')

try:
    for (env, ljs_bin, test) in tests:
        run_test(env, ljs_bin, test)
finally:
    print('')
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
