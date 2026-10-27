# -*- coding: utf-8 -*-
"""eval/ の test の共通設定: repo root と eval/ を import path に置く。"""

import sys
from pathlib import Path

EVAL_DIR = Path(__file__).resolve().parent.parent
REPO = EVAL_DIR.parent
for path in (REPO, EVAL_DIR):
    if str(path) not in sys.path:
        sys.path.insert(0, str(path))
