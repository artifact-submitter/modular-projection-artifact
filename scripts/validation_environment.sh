#!/usr/bin/env bash

# Bound Lake's regular build-job pool unless the caller selected another value.
# This setting is per process; it is not a process-tree thread or memory limit.
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
export LEAN_GC_THRESHOLD=${LEAN_GC_THRESHOLD:-256}
