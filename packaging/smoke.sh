#!/usr/bin/env bash
# Exercise the published CLI contract against a binary. Takes the binary to test, so it can
# be pointed at .lake/build/bin/stlc locally or at a freshly built artifact in CI:
#
#     packaging/smoke.sh .lake/build/bin/stlc
#
# This is the compiler's own check that it still honours what packaging/README.md promises.
# It is deliberately separate from the consumer's contract suite, which lives in the website
# repo and is run against this binary before anything is published: this file is what *we*
# guarantee, that one is what *they* depend on, and the two are allowed to differ.

set -euo pipefail

BIN="${1:?usage: smoke.sh PATH_TO_STLC}"
BIN="$(realpath "$BIN")"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

fail() { echo "smoke: FAIL: $*" >&2; exit 1; }
ok()   { echo "smoke: ok: $*"; }

# --- a valid program: exit 0, output on stdout -------------------------------------------
cat > "$WORK/valid.stlc" <<'EOF'
def id : ?0 → ?1 := λ x : ⋆ . x

def id2 : ?2 → ?3 := λ x : ?4 . id ( id x )
EOF

if ! out="$("$BIN" "$WORK/valid.stlc")"; then
  fail "a valid program exited non-zero"
fi
[ -n "$out" ] || fail "a valid program produced no output"
ok "valid program accepted"

# --- determinism: same input, same bytes -------------------------------------------------
out2="$("$BIN" "$WORK/valid.stlc")"
[ "$out" = "$out2" ] || fail "output differs between runs on identical input"
ok "deterministic"

# --- idempotence: stlc (stlc P) = stlc P -------------------------------------------------
printf '%s\n' "$out" > "$WORK/once.stlc"
twice="$("$BIN" "$WORK/once.stlc")" || fail "the compiler rejected its own output"
[ "$twice" = "$out" ] || fail "not idempotent: re-rendering changed the program"
ok "idempotent"

# --- an invalid program: non-zero, and nothing on stdout ---------------------------------
printf 'def broken : = := λ\n' > "$WORK/broken.stlc"
set +e
bad_out="$("$BIN" "$WORK/broken.stlc" 2>/dev/null)"
bad_rc=$?
set -e
[ "$bad_rc" -ne 0 ] || fail "an invalid program exited 0"
[ -z "$bad_out" ] || fail "an invalid program wrote to stdout: $bad_out"
ok "invalid program rejected, stdout clean"

# --- a missing file: non-zero ------------------------------------------------------------
set +e
"$BIN" "$WORK/does-not-exist.stlc" >/dev/null 2>&1
miss_rc=$?
set -e
[ "$miss_rc" -ne 0 ] || fail "a missing file exited 0"
ok "missing file rejected"

echo "smoke: all contract checks passed"
