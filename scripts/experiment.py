#!/usr/bin/env python3
"""Run one fixed experiment configuration, or print it without running."""
import argparse
import json
import os
import shlex
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    configs = json.loads((ROOT / 'experiments.json').read_text())
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('name', choices=configs)
    parser.add_argument('--print', action='store_true', dest='dry')
    args = parser.parse_args()
    config = configs[args.name]

    if 'derive_seeds_from' in config:
        if args.dry:
            print(f"Select non-certified, non-I10 seeds from {config['derive_seeds_from']} "
                  f"into {config['output']}")
            return
        with (ROOT / config['derive_seeds_from']).open() as source:
            rows = [json.loads(line) for line in source]
        output = ROOT / config['output']
        output.parent.mkdir(parents=True, exist_ok=True)
        if output.exists():
            parser.error(f'{output.relative_to(ROOT)} already exists; preserve it before rerunning')
        seeds = (row['seed'] for row in sorted(rows, key=lambda row: row['seed'])
                 if row['d13'] not in ('certified', 'I10'))
        with output.open('x') as target:
            target.write(''.join(f'{seed}\n' for seed in seeds))
        return

    argv = [sys.executable, *config['argv'][1:]]
    env = os.environ.copy()
    # Select the configured reading, independently of inherited experiment switches.
    env.pop('CHU_PLAN_D13_READING_A', None)
    env.pop('CHU_PLAN_D13_ORIGINAL', None)
    env.update(config.get('env', {}))
    display_env = ' '.join(f'{key}={shlex.quote(value)}'
                           for key, value in config.get('env', {}).items())
    print(f'{display_env} {shlex.join(argv)}'.strip(), flush=True)
    if args.dry:
        return
    log = ROOT / config['stdout']
    log.parent.mkdir(parents=True, exist_ok=True)
    (ROOT / 'out/figures').mkdir(parents=True, exist_ok=True)
    if log.exists():
        parser.error(f'{log.relative_to(ROOT)} already exists; preserve it before rerunning')
    with log.open('x') as output:
        result = subprocess.run(argv, cwd=ROOT, env=env, stdout=output,
                                stderr=subprocess.STDOUT)
    sys.exit(result.returncode)


if __name__ == '__main__':
    main()
