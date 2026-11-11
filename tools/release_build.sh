#!/usr/bin/env bash
# Builds what must build before a release of sledgehammer_fact_trigger (SKILL isabelle-patch-feature, 3.4 step 4).
set -euo pipefail
sessions=$(grep -v '^[[:space:]]*#' tools/required_sessions.txt | grep -v '^[[:space:]]*$')
"$ISABELLE" build -b -d tests $sessions
