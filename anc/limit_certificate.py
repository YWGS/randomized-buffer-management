import argparse
from fractions import Fraction as Q
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def logarithm_bounds(x, terms):
    require(1 <= x <= 3, "logarithm probe outside [1,3]")
    t = (x - 1) / (x + 1)
    square = t * t
    term = t
    total = Q(0)
    for j in range(terms):
        total += 2 * term / (2*j + 1)
        term *= square
    remainder = 2 * term / ((2*terms + 1) * (1-square))
    return total, total + remainder


def interval_for_H(q):
    z = 1 / (q-1)
    u = z+1
    terms = 8
    while True:
        u_lo, u_hi = logarithm_bounds(u, terms)
        z_lo, z_hi = logarithm_bounds(z, terms)
        j0_lo, j0_hi = u*u_lo-u+1, u*u_hi-u+1
        j1_lo, j1_hi = z*z_lo, z*z_hi
        if j0_hi < j1_lo:
            return j0_hi, j1_lo
        if j0_lo > j1_hi:
            return None
        terms *= 2


def dyadic_between(lo, hi):
    denominator = 1
    while True:
        k = (denominator * lo).__floor__() + 1
        x = Q(k, denominator)
        if x < hi:
            return x
        denominator *= 2


def choose_certificate(target):
    require(1 < target < 2, "expected 1 < target < 2")
    anchor = max(target, Q(3, 2))
    require(interval_for_H(anchor) is not None, "target exceeds the asymptotic bound")
    step = Q(1, 4)
    while True:
        q = anchor + step
        bracket = interval_for_H(q)
        if bracket is not None:
            break
        step /= 2
    j0_hi, j1_lo = bracket
    h = dyadic_between(j0_hi, j1_lo)
    d = 1/h
    z = 1/(q-1)
    u = z+1
    v = 4
    while j0_hi+(u-1)/v >= h or (1-Q(1,v))*j1_lo <= h:
        v *= 2
    x_lo = d*(u-1)/v
    per_event_gap = d*(u-target*z)/v
    n = max(2*v+3, ((x_lo + 1 + 2*target)/per_event_gap).__floor__()+1)
    return dict(target=str(target), probe=str(q), H=str(h), v=v, n=n)


def ceiling_ratio(x, y):
    return -(-x//y)


def grid_power(v, exponent, scale):
    lo = v*scale//(v-1)
    hi = ceiling_ratio(v*scale, v-1)
    a = b = scale
    while exponent:
        if exponent & 1:
            a = a*lo//scale
            b = ceiling_ratio(b*hi, scale)
        exponent //= 2
        if exponent:
            lo = lo*lo//scale
            hi = ceiling_ratio(hi*hi, scale)
    return a, b


def max_sum_enclosure(v, point, precision):
    while True:
        scale = 1 << precision
        low, high = 0, 3*v
        redo = False
        while high-low > 1:
            mid = (low+high)//2
            lo, hi = grid_power(v, mid, scale)
            if hi*point.denominator <= scale*point.numerator:
                low = mid
            elif lo*point.denominator >= scale*point.numerator:
                high = mid
            else:
                prev_hi = grid_power(v, mid-1, scale)[1]
                next_lo = grid_power(v, mid+1, scale)[0]
                if (prev_hi*point.denominator <= scale*point.numerator
                        <= next_lo*point.denominator):
                    low, high = mid-1, mid+1
                else:
                    redo = True
                break
        if not redo:
            break
        precision *= 2
    bounds = []
    for m in range(low, high):
        lo, hi = grid_power(v, m, scale)
        center = 1+m*point/v
        bounds.append((center-Q(hi,scale), center-Q(lo,scale)))
    return max(t[0] for t in bounds), max(t[1] for t in bounds)


def verify(cert):
    target, q, h = (Q(cert[key]) for key in ("target", "probe", "H"))
    v, n = cert["v"], cert["n"]
    require(type(v) is int and type(n) is int, "integer size parameters required")
    require(v>=4 and n>=2*v+3 and h>0 and 1<target<q<2 and q>=Q(3,2),
            "invalid witness parameters")
    d = 1/h
    z = 1/(q-1)
    u = z+1
    precision = 3*v.bit_length()+80
    for _ in range(5):
        f0_lo, f0_hi = max_sum_enclosure(v,u,precision)
        f1_lo, f1_hi = max_sum_enclosure(v,z,precision)
        if (u-1)/v+f0_hi < h < z-1+f1_lo:
            break
        require((u-1)/v+f0_lo < h < z-1+f1_hi, "invalid stationary probe")
        precision *= 2
    else:
        raise ValueError("stationary probe not resolved at the available precision")
    x_lo = d*(u-1)/v
    x_hi = d*(z-1)/v
    base = d/v
    numerator_floor = base+x_lo-(x_lo+1)/n
    denominator_ceiling = base+x_hi+Q(2,n)
    lower = numerator_floor/denominator_ceiling
    require(lower>target, "finite throughput margin is insufficient")
    spacing = d/(v*(v-1))
    return {"lambda": str(spacing), "finite_ratio_lower": str(lower)}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target", nargs="?", default="1.5422114197377450")
    parser.add_argument("--check", metavar="JSON", help="read an existing certificate")
    args=parser.parse_args()
    if args.check:
        with open(args.check, encoding="utf-8") as f:
            cert=json.load(f)
    else:
        cert=choose_certificate(Q(args.target))
    diagnostic=verify(cert)
    print(json.dumps(cert, indent=2))
    print("verified lambda =", diagnostic["lambda"])
    print("verified finite ratio lower bound =", diagnostic["finite_ratio_lower"])


if __name__ == "__main__":
    main()
