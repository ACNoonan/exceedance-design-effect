#!/usr/bin/env python3
"""Run an archived experiment with the topic directories on its import path.

Usage: python run.py --list
       python run.py theory/verify_indicator_icc.py [script arguments]
Inputs remain beside the script that reads them. This runner never downloads inputs.
Individual experiments may download data or models; read their source before running.
"""
from pathlib import Path
import argparse
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
TOPICS = ('theory', 'tails', 'prm', 'selection', 'empirical_core',
          'deploy_gate', 'nhanes', 'sw02ext', 'figures')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--list', action='store_true')
    parser.add_argument('script', nargs='?')
    parser.add_argument('arguments', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    scripts = sorted(p.relative_to(ROOT).as_posix()
                     for topic in TOPICS for p in (ROOT / topic).glob('*.py')
                     if not p.name.startswith('_'))
    if args.list:
        print('\n'.join(scripts))
        return 0
    if args.script not in scripts:
        parser.error('choose an archived script shown by --list')
    paths = [str(ROOT), *(str(ROOT / topic) for topic in TOPICS)]
    env = dict(os.environ, PYTHONPATH=os.pathsep.join(paths))
    return subprocess.run([sys.executable, str(ROOT / args.script), *args.arguments],
                          cwd=ROOT, env=env).returncode


if __name__ == '__main__':
    raise SystemExit(main())
