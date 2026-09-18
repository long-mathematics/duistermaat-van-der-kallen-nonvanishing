#!/usr/bin/env python3
"""Check bookkeeping coverage of labeled manuscript result environments.

This cannot verify semantic equivalence of Lean statements and the manuscript.
That mathematical audit is recorded in FORMALIZATION_STATUS.md.
"""
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
source = (root / 'duistermaat_van_der_kallen_nonvanishing.tex').read_text()
ledger = (root / 'FORMALIZATION_STATUS.md').read_text()
pattern = re.compile(
    r'\\begin\{(theorem|lemma|proposition|corollary|definition|standard|remark)\}'
    r'(?:\[[^\]]*\])?\s*\\label\{([^}]+)\}')
labels = [label for _, label in pattern.findall(source)]
missing = [label for label in labels if f'`{label}`' not in ledger]
if missing:
    raise SystemExit('Missing result labels from coverage ledger: ' + ', '.join(missing))
for required in ['INCOMPLETE', 'RadiusTailObligation', 'SpherePathObligation',
                 'OPTIONAL / EXCLUDED', 'CONDITIONAL']:
    if required not in ledger:
        raise SystemExit('Missing explicit status marker: ' + required)
print(f'Coverage bookkeeping passed: {len(labels)} labeled result environments represented.')
