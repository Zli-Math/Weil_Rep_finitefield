#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
lake build WeilRepFinitefield.Examples.F2 WeilRepFinitefield.Examples.Cocycle
