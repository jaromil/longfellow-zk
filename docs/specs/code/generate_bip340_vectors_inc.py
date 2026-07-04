#!/usr/bin/env python3
"""Regenerate testdata/bip340_vectors.inc from bip340_test_vectors.csv."""
import csv
import os
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.join(SCRIPT_DIR, '..', '..', '..', '..')
CSV_PATH = os.path.join(REPO_ROOT, 'lib', 'circuits', 'bip340', 'testdata',
                         'bip340_test_vectors.csv')
INC_PATH = os.path.join(REPO_ROOT, 'lib', 'circuits', 'bip340', 'testdata',
                         'bip340_vectors.inc')

with open(CSV_PATH, newline='', encoding='ascii') as f:
    reader = csv.DictReader(f)
    rows = list(reader)

assert len(rows) == 19, f'Expected 19 vectors, got {len(rows)}'

# Vectors with known eval-backend crashes (circuit_can_check=false).
EVAL_CRASH_VECTORS = {4, 15, 16, 17, 18}

with open(INC_PATH, 'w') as f:
    f.write('// Auto-generated from bip340_test_vectors.csv.  Do not edit.\n')
    f.write(f'// Regenerate: {os.path.basename(__file__)}\n')
    f.write('\n')
    for i, row in enumerate(rows):
        pk = row['public_key']
        msg = row['message']
        sig = row['signature']
        valid = 'true' if row['verification_result'].upper() == 'TRUE' else 'false'
        cc = 'false' if i in EVAL_CRASH_VECTORS else 'true'

        comment = row.get('comment', '')
        f.write(f'    // {i}: {comment}\n')

        sig_line1 = sig[:64]
        sig_line2 = sig[64:]

        if msg:
            msg_quoted = f'"{msg}"'
        else:
            msg_quoted = '""'

        if len(msg) <= 80:
            f.write(f'    {{{pk},\n'
                    f'     {msg_quoted},\n'
                    f'     "{sig_line1}"\n'
                    f'     "{sig_line2}", {valid}, {cc}}},\n')
        else:
            # Long message: split across lines.
            f.write(f'    {{{pk},\n')
            for j in range(0, len(msg), 64):
                chunk = msg[j:j+64]
                if j + 64 < len(msg):
                    f.write(f'     "{chunk}"\n')
                else:
                    f.write(f'     "{chunk}",\n')
            f.write(f'     "{sig_line1}"\n'
                    f'     "{sig_line2}", {valid}, {cc}}},\n')

print(f'Regenerated {INC_PATH} from {CSV_PATH} ({len(rows)} vectors)')
