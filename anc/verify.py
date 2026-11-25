
import argparse
from fractions import Fraction
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
MATHLIB_REVISION = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MODULES = [
    "stock", "stockRun", "finite", "finitePhysical", "finiteSwitch",
    "stockPolicy", "finiteThroughput", "Family", "Offline", "PaperNumbers",
    "Repeat", "Ratio", "finiteGeneral", "limit_bridge", "Assemble", "Cohorts",
    "LargeBuffer", "PhysicalFamily", "PhysicalOnline", "OfflineRun", "PacketTrace",
    "OutcomeTable", "PhysicalOffline", "PolicyBridge",
]


def check_axioms(output, required=()):
    reports = {}
    for name, names, empty in re.findall(
        r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))",
        output,
    ):
        deps = set() if empty else {axiom.strip() for axiom in names.split(",") if axiom.strip()}
        unexpected = deps - STANDARD_AXIOMS
        if unexpected:
            raise SystemExit(f"{name} uses unexpected axioms: {sorted(unexpected)}")
        reports[name] = deps
    missing = set(required) - reports.keys()
    if missing:
        raise SystemExit(f"No kernel axiom report for: {sorted(missing)}")


def audit_final_theorem(lean, mathlib, build, env):
    final = "SharedBuffer.PolicyBridge.sharpFromPolicies"
    source = Path(build) / "SubmissionAudit.lean"
    source.write_text("""import PolicyBridge

open SharedBuffer

theorem SubmissionAudit.checked {R : ℝ} (hR : 0 ≤ R)
    (uniform : ∀ B K : ℕ, 0 < B → 0 < K →
      ∃ (p : Packet.PolicyLaw B (List.finRange K)) (h : ℝ), Packet.Competitive p R h) :
    ∃ r : ℝ, 3/2 < r ∧ r < 2 ∧ Ratio.entropy r = 1 ∧
      (∀ t, 1 < t → Ratio.entropy t = 1 → t = r) ∧ r ≤ R :=
  @PolicyBridge.sharpFromPolicies R hR uniform

theorem SubmissionAudit.noThreeHalves :
    ¬ (∀ B K : ℕ, 0 < B → 0 < K →
      ∃ (p : Packet.PolicyLaw B (List.finRange K)) (h : ℝ), Packet.Competitive p (3/2) h) := by
  intro uniform
  obtain ⟨r, hr, _, _, _, hle⟩ := SubmissionAudit.checked (R := 3/2) (by norm_num) uniform
  exact (not_le_of_gt hr) hle

#print axioms SharedBuffer.PolicyBridge.sharpFromPolicies
#print axioms SubmissionAudit.checked
#print axioms SubmissionAudit.noThreeHalves
""", encoding="utf-8")
    run = subprocess.run([lean, "-DwarningAsError=true", "-R", build, str(source)],
                         cwd=mathlib, env=env, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True)
    print("Final theorem type and transitive axioms", run.stdout.strip(), sep="\n", flush=True)
    run.check_returncode()
    check_axioms(run.stdout, (final, "SubmissionAudit.checked", "SubmissionAudit.noThreeHalves"))


def compile_modules(mathlib, tools_directory):
    env = os.environ.copy()
    if tools_directory:
        env["PATH"] = os.pathsep.join([str(tools_directory.resolve()), env["PATH"]])
    lean = shutil.which("lean", path=env["PATH"])
    lake = shutil.which("lake", path=env["PATH"])
    if not (lean and lake):
        raise SystemExit("Place Lean 4.19.0 and Lake on PATH, or pass --lean-bin.")
    version = subprocess.check_output([lean, "--version"], cwd=mathlib, env=env, text=True).strip()
    if not re.search(r"\bversion 4\.19\.0\b", version):
        raise SystemExit("Expected Lean 4.19.0; found " + version)
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=mathlib, text=True).strip()
    if revision != MATHLIB_REVISION:
        raise SystemExit("Use mathlib4 v4.19.0 at " + MATHLIB_REVISION)
    paths = subprocess.check_output(
        [lake, "env", sys.executable, "-c", "import os; print(os.environ['LEAN_PATH'])"],
        cwd=mathlib, env=env, text=True,
    ).strip()
    print(version, flush=True)
    with tempfile.TemporaryDirectory(prefix="shared-buffer-") as build:
        env["LEAN_PATH"] = os.pathsep.join([build, paths])
        for name in MODULES:
            args = [
                lean, "-DwarningAsError=true", "-R", str(HERE),
                "-o", str(Path(build) / (name + ".olean")), str(HERE / (name + ".lean")),
            ]
            run = subprocess.run(args, cwd=mathlib, env=env, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT, text=True)
            print(name, run.stdout.strip(), sep="\n", flush=True)
            run.check_returncode()
            check_axioms(run.stdout)
        audit_final_theorem(lean, mathlib, build, env)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib", required=True, type=Path,
                        help="mathlib4 v4.19.0 Git checkout with compiled library caches")
    parser.add_argument("--lean-bin", type=Path, help="optional directory containing lean and lake")
    args = parser.parse_args()
    compile_modules(args.mathlib.resolve(), args.lean_bin)
    for command in (["finite_witness.py"], ["limit_certificate.py", "1.5422114197377451"],
                    ["tiny_bayes.py"], ["guarded_replay.py"], ["check_bounded_arrivals.py"]):
        subprocess.run([sys.executable, "-B", *command], cwd=HERE, check=True)

    sys.dont_write_bytecode = True
    from limit_certificate import interval_for_H
    if (interval_for_H(Fraction("1.5422114197377451")) is None
            or interval_for_H(Fraction("1.5422114197377452")) is not None):
        raise SystemExit("The rational log enclosures failed to bracket the root.")
    print("1.5422114197377451 < r < 1.5422114197377452")
    print(f"PASS: {len(MODULES)} Lean modules, five numerical checks and the root bracket.")


if __name__ == "__main__":
    main()
