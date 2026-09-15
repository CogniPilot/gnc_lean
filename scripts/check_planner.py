"""Exercise the Lean CLI and compare it with the recorded figure-eight seed.

Run after `lake build` inside `nix develop`. These are interface/regression
checks; PolynomialKernel.lean supplies the universal arithmetic proofs.
Only the Python standard library is needed.
"""
from fractions import Fraction as Q
import json
from math import factorial
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent


def invoke(*args, valid=True):
    process = subprocess.run(
        ["lake", "env", "lean", "--run", "GNC/Tools/Planner.lean", *map(str, args)],
        cwd=ROOT, capture_output=True, text=True,
    )
    if not valid:
        assert process.returncode != 0 and process.stderr.strip(), process.stdout
        return
    assert process.returncode == 0, process.stdout + process.stderr
    result = json.loads(process.stdout)
    assert result["arithmetic"] == "exact rational"
    return result, [Q(v["value"]) for v in result["physical_jets"]]


def main():
    calls = 0
    for a, b, length in [(Q(-1, 4), Q(-1, 4), Q(10)),
                         (Q(2, 7), Q(-3, 5), Q(17, 3)), (Q(0), Q(0), Q(1))]:
        for distance, second in [(Q(0), a), (length, b)]:
            result, values = invoke(a, b, length, distance, 8)
            calls += 1
            assert Q(result["a"]) == a and Q(result["b"]) == b
            assert Q(result["length"]) == length
            assert Q(result["nominal_distance"]) == distance
            assert values[:4] == [0, 0, second, 0], values
            assert values[8] == 0
    result, values = invoke("1/-4", "-1/4", 10, 5, 32)
    calls += 1
    assert values[:5] == [Q(-75, 64), 0, Q(7, 32), 0, Q(-3, 40)]
    assert all(x == 0 for x in values[8:])
    for args in [(), ("1/0", 0, 1, 0, 4), ("bad", 0, 1, 0, 4),
                 (0, 0, 0, 0, 4), (0, 0, -1, 0, 4),
                 (0, 0, 1, 0, -1), (0, 0, 1, 0, 33)]:
        invoke(*args, valid=False)
        calls += 1

    # Recover independently chosen physical polynomials from their endpoint
    # derivatives. This detects endpoint ordering and length-scaling errors
    # without repeating the Hermite coefficient formula in the test.
    def derivative(cs, q, n):
        return sum((cs[j] * factorial(j) / factorial(j-n) * q**(j-n)
                    for j in range(n, len(cs))), Q(0))

    for cs, length in [([Q(j-3, j+1) for j in range(8)], Q(7, 3)),
                       ([Q(2), Q(-3), Q(5)]+[Q(0)]*5, Q(1, 7)),
                       ([Q(0)]*7+[Q(1)], Q(11, 2))]:
        start = [derivative(cs, Q(0), n) for n in range(4)]
        finish = [derivative(cs, length, n) for n in range(4)]
        for q in [Q(0), length/3, length, -length/2]:
            result, values = invoke("hermite", ",".join(map(str, start)),
                                    ",".join(map(str, finish)), length, q, 9)
            calls += 1
            assert [Q(c) for c in result["normalized_coefficients"]] == [
                c*length**j for j, c in enumerate(cs)]
            assert [Q(c) for c in result["start_jet"]] == start
            assert [Q(c) for c in result["end_jet"]] == finish
            assert values == [derivative(cs, q, n) for n in range(10)]
    for args in [("0,0,0", "0,0,0,0", 1, 0, 4),
                 ("0,0,0,0,0", "0,0,0,0", 1, 0, 4),
                 ("0,0,1/0,0", "0,0,0,0", 1, 0, 4),
                 ("0,0,0,0", "0,0,0,0", 0, 0, 4),
                 ("0,0,0,0", "0,0,0,0", 1, 0, 33)]:
        invoke("hermite", *args, valid=False)
        calls += 1

    print(json.dumps({"cli_cases": calls,
                      "status": "passed; exact-rational planner interface checks"}, indent=2))


if __name__ == "__main__":
    main()
