#!/usr/bin/env python3
"""Finite regression checker for the Pascal Minus-One GCD conjecture.

This is evidence and debugging infrastructure, not a proof.
"""
from __future__ import annotations

import argparse
import math
from dataclasses import dataclass


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def vp(n: int, p: int) -> int:
    if n <= 0 or not is_prime(p):
        raise ValueError("vp expects n > 0 and prime p")
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def base_digits(n: int, p: int) -> list[int]:
    if p < 2:
        raise ValueError("base must be at least 2")
    out: list[int] = []
    while n:
        out.append(n % p)
        n //= p
    return out


def parity_digit_sums(n: int, p: int) -> tuple[int, int]:
    ds = base_digits(n, p)
    return sum(ds[0::2]), sum(ds[1::2])


def predicted_valuation(N: int, m: int, p: int) -> int:
    A, B = parity_digit_sums(N, p)
    if (A, B) == (1, 1) and p == m - 1:
        return 2
    if (A, B) == (1, 1) and p > m:
        return 1
    if (A, B) in {(m, 0), (0, m)}:
        return 1
    return 0


def actual_valuation(N: int, m: int, p: int) -> int:
    vals = [vp(math.comb(N, k), p) for k in range(m, N, m)]
    if not vals:
        raise ValueError("the theorem regime N > m, m | N should give an admissible k")
    return min(vals)


def borrow_count(N: int, k: int, p: int) -> int:
    """Count borrows in base-p subtraction N-k (equivalently carries in k+(N-k))."""
    if not (0 <= k <= N):
        raise ValueError("need 0 <= k <= N")
    borrow = 0
    count = 0
    n, x = N, k
    while n or x or borrow:
        nd = n % p
        kd = x % p
        if kd + borrow > nd:
            count += 1
            borrow = 1
        else:
            borrow = 0
        n //= p
        x //= p
    return count


def edge_uniform_witness(N: int, m: int, p: int) -> tuple[int, int, int] | None:
    """Return (t,s,k) for the repaired p=m-1 uniform witness when applicable."""
    if p != m - 1:
        return None
    A, B = parity_digit_sums(N, p)
    if (A, B) not in {(m, 0), (0, m)}:
        return None
    ds = base_digits(N, p)
    occupied = [i for i, d in enumerate(ds) if d]
    if len(occupied) < 2:
        return None
    t = occupied[-1]
    candidates = [s for s in occupied[:-1] if s % 2 == t % 2]
    if not candidates or t == 0:
        return None
    s = candidates[-1]
    k = p ** (t - 1) + p**s
    return t, s, k


@dataclass(frozen=True)
class Failure:
    N: int
    m: int
    p: int
    actual: int
    predicted: int


def sweep(max_m: int, max_n: int, max_p: int) -> tuple[int, list[Failure], int, list[tuple[int, int, int, int]]]:
    checked = 0
    failures: list[Failure] = []
    edge_checked = 0
    edge_failures: list[tuple[int, int, int, int]] = []
    primes = [p for p in range(2, max_p + 1) if is_prime(p)]
    for m in range(3, max_m + 1):
        for N in range(2 * m, max_n + 1, m):
            for p in primes:
                if p % m != m - 1:
                    continue
                checked += 1
                got = actual_valuation(N, m, p)
                want = predicted_valuation(N, m, p)
                if got != want:
                    failures.append(Failure(N, m, p, got, want))
                witness = edge_uniform_witness(N, m, p)
                if witness is not None:
                    edge_checked += 1
                    _, _, k = witness
                    ok = 0 < k < N and k % m == 0 and borrow_count(N, k, p) == 1
                    if not ok:
                        edge_failures.append((N, m, p, k))
    return checked, failures, edge_checked, edge_failures


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-m", type=int, default=14)
    ap.add_argument("--max-n", type=int, default=500)
    ap.add_argument("--max-p", type=int, default=43)
    args = ap.parse_args()
    checked, failures, edge_checked, edge_failures = sweep(args.max_m, args.max_n, args.max_p)
    print(f"theorem cases checked: {checked}")
    print(f"theorem failures: {len(failures)}")
    print(f"edge witnesses checked: {edge_checked}")
    print(f"edge witness failures: {len(edge_failures)}")
    if failures:
        print("first theorem failure:", failures[0])
    if edge_failures:
        print("first edge witness failure:", edge_failures[0])
    return 1 if failures or edge_failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
