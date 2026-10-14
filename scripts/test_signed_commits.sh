#!/usr/bin/env bash
# Selftest for scripts/verify_signed_commits.py.
#
# Uses an explicitly isolated temp GNUPGHOME for all key material and an
# isolated throwaway repository, so the production keyring and the real
# checkout are never touched.  Covers:
#   1. deliberately unsigned branch            -> gate must FAIL
#   2. signed commits, key untrusted (U case)  -> gate must PASS
#   3. signed merge commit (git merge --no-ff -S, divergent branches)
#                                              -> merge in checked range, PASS
#   4. range isolation: unsigned commit in ancestors of base is NOT checked
#   5. known signed commits from the real repository (U + web-flow merge) -> PASS
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SCRIPT="$REPO_ROOT/scripts/verify_signed_commits.py"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/signed-commits-selftest.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

export GNUPGHOME="$WORK/gnupg"
mkdir -p "$GNUPGHOME" && chmod 700 "$GNUPGHOME"

pass=0; fail=0
ok()   { echo "PASS: $1"; pass=$((pass+1)); }
bad()  { echo "FAIL: $1"; fail=$((fail+1)); }
expect_exit() { # desc expected_exit cmd...
  local desc="$1" want="$2"; shift 2
  local got=0
  "$@" || got=$?
  if [ "$got" -eq "$want" ]; then ok "$desc (exit $got)"; else bad "$desc (exit $got, want $want)"; fi
}

echo "== generating isolated test key =="
cat > "$WORK/keyparams" <<EOF
%no-protection
Key-Type: eddsa
Key-Curve: ed25519
Name-Real: Signed Commits Selftest
Name-Email: selftest@localhost
Expire-Date: 0
%commit
EOF
gpg --batch --gen-key "$WORK/keyparams" 2>/dev/null
gpg --armor --export selftest@localhost > "$WORK/selftest.pub"
echo "test key: $(gpg --show-keys --with-colons "$WORK/selftest.pub" | awk -F: '/^fpr:/ {print $10; exit}')"

echo "== building isolated test repo =="
TREPO="$WORK/repo"
git init -q "$TREPO"
git -C "$TREPO" config user.name "Selftest"
git -C "$TREPO" config user.email "selftest@localhost"
git -C "$TREPO" config commit.gpgsign false
git -C "$TREPO" config gpg.format openpgp
git -C "$TREPO" config gpg.program gpg
git -C "$TREPO" config user.signingkey "$(gpg --show-keys --with-colons "$WORK/selftest.pub" | awk -F: '/^fpr:/ {print $10; exit}')"
echo base > "$TREPO/base.txt"
git -C "$TREPO" add base.txt
git -C "$TREPO" commit -q -m "base commit"
BASE=$(git -C "$TREPO" rev-parse HEAD)

echo "== 1. deliberately unsigned branch must FAIL =="
echo one > "$TREPO/one.txt"
git -C "$TREPO" add one.txt
git -C "$TREPO" commit -q -m "unsigned commit"
UNSIGNED=$(git -C "$TREPO" rev-parse HEAD)
expect_exit "unsigned branch rejected" 1 \
  python3 "$SCRIPT" --repo "$TREPO" --base "$BASE" --head "$UNSIGNED" --extra-key "$WORK/selftest.pub"

echo "== 2. signed commits with unknown-local-trust key (U case) must PASS =="
git -C "$TREPO" checkout -q -b signed "$BASE"
echo two > "$TREPO/two.txt"
git -C "$TREPO" add two.txt
git -C "$TREPO" -c commit.gpgsign=true commit -q -m "signed commit one"
echo three > "$TREPO/three.txt"
git -C "$TREPO" add three.txt
git -C "$TREPO" -c commit.gpgsign=true commit -q -m "signed commit two"
SIGNED=$(git -C "$TREPO" rev-parse HEAD)
for c in $(git -C "$TREPO" rev-list "$BASE..$SIGNED"); do
  st=$(git -C "$TREPO" log -1 --format=%G? "$c")
  [ "$st" = "U" ] || { echo "note: commit $c status=$st (expected U)"; }
done
expect_exit "U-case signed commits accepted" 0 \
  python3 "$SCRIPT" --repo "$TREPO" --base "$BASE" --head "$SIGNED" --extra-key "$WORK/selftest.pub"

echo "== 3. signed merge commit (divergent branches, git merge --no-ff -S) must PASS =="
git -C "$TREPO" checkout -q -b side "$BASE"
echo side > "$TREPO/side.txt"
git -C "$TREPO" add side.txt
git -C "$TREPO" -c commit.gpgsign=true commit -q -m "signed side commit"
SIDE=$(git -C "$TREPO" rev-parse HEAD)
git -C "$TREPO" checkout -q signed
git -C "$TREPO" -c commit.gpgsign=true merge -q --no-ff -S -m "signed merge of side" "$SIDE"
MERGE=$(git -C "$TREPO" rev-parse HEAD)
nparents=$(git -C "$TREPO" log -1 --format=%P "$MERGE" | wc -w)
[ "$nparents" -eq 2 ] || { bad "merge has $nparents parents, want 2"; echo "FAIL: selftest setup broken"; exit 1; }
nmerges=$(git -C "$TREPO" rev-list --min-parents=2 "$BASE..$MERGE" | wc -l)
[ "$nmerges" -ge 1 ] || { bad "no merge commit in $BASE..$MERGE"; echo "FAIL: selftest setup broken"; exit 1; }
mst=$(git -C "$TREPO" log -1 --format=%G? "$MERGE")
echo "merge commit $MERGE status=$mst parents=$nparents"
expect_exit "signed merge commit accepted" 0 \
  python3 "$SCRIPT" --repo "$TREPO" --base "$BASE" --head "$MERGE" --extra-key "$WORK/selftest.pub"

echo "== 3b. signed merge with UNSIGNED side branch must FAIL (dangerous topology) =="
git -C "$TREPO" checkout -q -b unsigned-side "$BASE"
echo uside > "$TREPO/uside.txt"
git -C "$TREPO" add uside.txt
git -C "$TREPO" commit -q -m "UNSIGNED side commit"
USIDE=$(git -C "$TREPO" rev-parse HEAD)
git -C "$TREPO" checkout -q signed
git -C "$TREPO" -c commit.gpgsign=true merge -q --no-ff -S -m "signed merge of unsigned side" "$USIDE"
UMERGE=$(git -C "$TREPO" rev-parse HEAD)
uparents=$(git -C "$TREPO" log -1 --format=%P "$UMERGE" | wc -w)
[ "$uparents" -eq 2 ] || { bad "merge has $uparents parents, want 2"; echo "FAIL: selftest setup broken"; exit 1; }
expect_exit "signed merge with unsigned side branch rejected" 1 \
  python3 "$SCRIPT" --repo "$TREPO" --base "$BASE" --head "$UMERGE" --extra-key "$WORK/selftest.pub"

echo "== 4. range isolation: unsigned ancestor of base must NOT be checked =="
# UNSIGNED sits on master below a fresh base2; the signed range above base2
# must pass even though an unsigned commit is an ancestor of the base ref.
git -C "$TREPO" checkout -q master 2>/dev/null || git -C "$TREPO" checkout -q main
git -C "$TREPO" merge-base --is-ancestor "$UNSIGNED" HEAD || { bad "setup: unsigned not on master"; exit 1; }
echo base2 > "$TREPO/base2.txt"
git -C "$TREPO" add base2.txt
git -C "$TREPO" commit -q -m "base2 commit"
BASE2=$(git -C "$TREPO" rev-parse HEAD)
git -C "$TREPO" merge-base --is-ancestor "$UNSIGNED" "$BASE2" || { bad "setup: unsigned not ancestor of base2"; exit 1; }
git -C "$TREPO" checkout -q -b iso "$BASE2"
echo iso > "$TREPO/iso.txt"
git -C "$TREPO" add iso.txt
git -C "$TREPO" -c commit.gpgsign=true commit -q -m "signed iso commit"
ISO=$(git -C "$TREPO" rev-parse HEAD)
expect_exit "unsigned ancestor of base not checked" 0 \
  python3 "$SCRIPT" --repo "$TREPO" --base "$BASE2" --head "$ISO" --extra-key "$WORK/selftest.pub"

echo "== 4b. pinning must reject unexpected fingerprint and extra primary keys =="
cat "$REPO_ROOT/scripts/trusted-keys/github-web-flow.asc" \
    "$REPO_ROOT/scripts/trusted-keys/maintainer-ottojung.asc" > "$WORK/multi.pub"
if python3 - "$SCRIPT" "$WORK/selftest.pub" "$WORK/multi.pub" <<'PYKEY'
import importlib.util,os,sys,tempfile
spec=importlib.util.spec_from_file_location("gate",sys.argv[1])
gate=importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
def must_reject(path,fp,label):
    gate.TRUSTED_KEYS=((path,fp,label),)
    with tempfile.TemporaryDirectory(prefix="badkey.") as home:
        os.chmod(home,0o700)
        try: gate.fetch_keyring(home)
        except gate.AuditError as e:
            print("rejected",label,":",str(e)[:130])
            return
        raise AssertionError("UNEXPECTED ACCEPTANCE: "+label)
must_reject(sys.argv[2],"0000000000000000000000000000000000000000","wrong fingerprint")
must_reject(sys.argv[3],"968479A1AFF927E37D1A566BB5690EEEBB952194","extra primary key")
PYKEY
then
  ok "fingerprint mismatch and multiple-primary bundle rejected"
else
  bad "pinned key file negative tests"
fi

echo "== 5. known signed commits from the real repository must PASS =="
REAL="$REPO_ROOT"
expect_exit "real signed PR #161 commit 96a5a7b accepted" 0 \
  python3 "$SCRIPT" --repo "$REAL" --base 96a5a7b~1 --head 96a5a7b
# PR #160 range: 10 commits (incl. merges), every one cryptographically signed.
expect_exit "real all-signed PR #160 range accepted" 0 \
  python3 "$SCRIPT" --repo "$REAL" --base 080b1b3 --head e70257b

echo
echo "selftest summary: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
