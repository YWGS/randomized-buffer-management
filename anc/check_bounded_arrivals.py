from bisect import bisect_left, bisect_right
from fractions import Fraction


def pattern(v, groups, outputs, buffer, coefficient):
    remaining = outputs
    sizes, epochs = [], [0]
    continuing = 0
    spacing = coefficient / (v * v)
    for _ in range(groups):
        size = remaining // v
        if size == 0:
            raise ValueError('Too few outputs for this number of groups')
        remaining -= size
        denominator = size * spacing.denominator
        gap = max(1, (buffer * spacing.numerator + denominator // 2) // denominator)
        sizes.append(size)
        epochs.append(epochs[-1] + gap)
        continuing += remaining * gap
    return sizes, epochs, continuing


def occupancy(sizes, epochs, totals, rate):
    load = [0] * len(epochs)
    for j, (size, total) in enumerate(zip(sizes, totals)):
        if total == 0:
            continue
        epoch = epochs[j]
        before = (total - 1) // (rate * size)
        after = (total - 1) // size
        oldest = bisect_left(epochs, epoch - before)
        latest = bisect_right(epochs, epoch + after)
        for i in range(oldest, j):
            load[i] += total - size * rate * (epoch - epochs[i])
        for i in range(j, latest):
            load[i] += total - size * (epochs[i] - epoch)
    return max(load, default=0)


def certificate(v, groups, outputs, fan_in, coefficient, trial, history):
    buffer = 100_000 * outputs
    sizes, epochs, base = pattern(v, groups, outputs, buffer, coefficient)
    q = int((buffer - outputs) * trial)
    stocks = [q if q <= (fan_in - 1) * size * epoch else 0
              for size, epoch in zip(sizes, epochs)]
    load = occupancy(sizes, epochs, stocks, fan_in - 1)
    if load > buffer - outputs:
        stocks = [s * (buffer - outputs) // load for s in stocks]
    assert occupancy(sizes, epochs, stocks, fan_in - 1) + outputs <= buffer
    assert all(s <= (fan_in - 1) * d * t for s, d, t in zip(stocks, sizes, epochs))
    offline = base + sum(stocks)
    loss = 0
    for i in range(groups):
        loss += sum(sizes[j] * (epochs[i] - epochs[j])
                    for j in range(max(0, i - history), i))
    assert 0 <= history < groups
    missing = history * (history + 1) // 2
    upper = base + buffer + (groups * buffer + loss + Fraction(missing * buffer, v)) / (v + history)
    return Fraction(offline, upper)


def main():
    if not __debug__:
        raise RuntimeError('Run with assertions enabled')
    cases = [
        (60, 4600, 10**37, 7, Fraction(8, 5), Fraction(30876, 10**6), 25),
        (100, 7000, 10**36, 32, Fraction(1), Fraction(16693, 10**6), 56),
        (120, 4800, 10**22, 64, Fraction(1), Fraction(14107, 10**6), 68),
    ]
    for case in cases:
        ratio = certificate(*case)
        if case[3] == 7:
            assert ratio * ratio > 2
        else:
            assert ratio > Fraction(3, 2)
        print(f'{case[3]} packets per output per slot, {case[2]} active outputs, '
              f'{case[1]} main groups: {float(ratio):.10f} (exact comparison passed)')


if __name__ == '__main__':
    main()
