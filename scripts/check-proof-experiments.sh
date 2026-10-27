#!/usr/bin/env bash
# Run from the repository root, with the current self-hosted compiler.
set -euo pipefail

compiler=${1:-out/jihoo}

proof_output=$("$compiler" run experimental/proofs/example.jh -I experimental/kernel)
expected_proof=$'checked at compile time: 2 theorems, 2 general statements, 1 induction, 5 proof steps\nadd_zero: for every n, add(n, zero) = n\ntwice_zero: for every n, add(add(n, zero), zero) = n'
if [[ "$proof_output" != "$expected_proof" ]]; then
    printf 'Unexpected proof example output:\n%s\n' "$proof_output" >&2
    exit 1
fi

codec_output=$("$compiler" run experimental/verified-codec/example.jh -I experimental/proofs -I experimental/kernel -- 0)
expected_codec=$'Red encodes to 2\nGreen\nround trip: true'
if [[ "$codec_output" != "$expected_codec" ]]; then
    printf 'Unexpected codec example output:\n%s\n' "$codec_output" >&2
    exit 1
fi

printf 'Proof and generated-codec smoke tests passed\n'
