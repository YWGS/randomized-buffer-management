from bisect import bisect_left, bisect_right
from fractions import Fraction as F


def check():
    v, n, m = 20, 1600, 11
    K, B0 = 20**1600, 400*380**1599
    ds = [20**(n-1-i)*19**i for i in range(n)] + [19**n]
    ts = [0]
    for i in range(n):
        ts.append(ts[-1] + 20**i*19**(n-1-i))
    assert sum(ds) == K
    q = (B0-K)*333//4000
    L = 1
    ingress = L*B0+1
    N = ingress*K
    for h, s in [(1, 0), (100, B0-1), (K+1, B0-1)]:
        B = h*B0+s
        guard = (h+L-1)//L
        dates = [h*t+(j+1)*guard for j,t in enumerate(ts)]
        target = h*q
        stock = [0]*len(dates)
        for j,d in enumerate(ds[:-1]):
            e = dates[j]
            left = bisect_left(dates, e - (target-1)//(d*(ingress-1)))
            right = bisect_right(dates, e + (target-1)//d)
            for i in range(left, right):
                age = dates[i]-e
                stock[i] += max(target - d*(age if age>=0 else (ingress-1)*(-age)), 0)
            assert target <= d*(ingress-1)*e
        assert max(stock)+K <= B
        base = sum(d*t for d,t in zip(ds,dates))
        cost = sum(ds[j]*(dates[i]-dates[j]) for i in range(n)
                   for j in range(max(0,i-m),i))
        upper = base+B + (F(n*B+cost)+F(m*(m+1)*B,2*v))/(v+m)
        lower = base+n*target
        ratio = F(lower)/upper
        assert n>=m and min(ds)>0
        if B>=N:
            assert ratio>F(3,2)
        print(f"guarded replay: B>=N={B>=N}, nonzero capacity remainder={bool(s)}, "
              f"offline pre-service capacity PASS at {n+1} events, bound {float(ratio):.10f}")
    assert B>=N


if __name__ == "__main__":
    check()
