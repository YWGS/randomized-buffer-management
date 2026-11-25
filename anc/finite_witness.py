from fractions import Fraction


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def verify():
    v, w, n, m = 20, 19, 1600, 11
    capacity = 400 * 380 ** (n - 1)
    labels = v ** n
    sizes = [v ** (n - 1 - i) * w ** i for i in range(n)] + [w ** n]
    lengths = [v ** i * w ** (n - 1 - i) for i in range(n)]
    times = [0]
    for duration in lengths:
        times.append(times[-1] + duration)
    require(sum(sizes) == labels < capacity, 'switch size')
    require(all(d * length * 400 == capacity
                for d, length in zip(sizes, lengths)), 'slot geometry')
    prior_service = sum(d * t for d, t in zip(sizes, times))
    require(400 * prior_service == 19 * n * capacity, 'total pre-expiration service')

    load = (capacity - labels) * 333 // 4000
    receivers = labels
    stocks = []
    largest_live_cohort_count = 0
    for i, d in enumerate(sizes):
        require(receivers == (v*d if i < n else d), 'receiver count')
        receivers -= d
        if i < n:
            stocks.append((d, load))
        require(receivers + sum(stock for _, stock in stocks) <= capacity,
                'infeasible offline service at event {}'.format(i))
        largest_live_cohort_count = max(largest_live_cohort_count, len(stocks))
        if i < n:
            elapsed = lengths[i]
            stocks = [(count, stock-count*elapsed) for count, stock in stocks
                      if stock > count*elapsed]
    require(receivers == 0 and all(stock <= count*capacity for count, stock in stocks),
            'final B-slot drain')
    offline = prior_service + n * load

    lag_cost = [0] + [sizes[0]*(times[k]-times[0]) for k in range(1,m+1)]
    coefficient = [0] * n
    rhs = 0
    for i in range(n):
        coefficient[i] += v*v
        rhs += v*capacity
        for k in range(1, min(m,i)+1):
            col = i-k
            cost = sizes[col] * (times[i]-times[col])
            require(cost == lag_cost[k], 'lag identity')
            coefficient[col] += v
            rhs += v*cost
    target = v*(v+m)
    tail_multipliers = 0
    for col, weight in enumerate(coefficient):
        missing, remainder = divmod(target-weight, v)
        require(missing >= 0 and remainder == 0, 'tail multiplier')
        coefficient[col] += v*missing
        rhs += capacity*missing
        tail_multipliers += missing
    require(coefficient == [target]*n and tail_multipliers == m*(m+1)//2,
            'Farkas coefficients')
    common_cost = capacity + sum(lag_cost)
    padded_rhs = v*n*common_cost + tail_multipliers*capacity
    require(rhs <= padded_rhs, 'padded dual')
    upper = Fraction(prior_service + capacity) + Fraction(padded_rhs, target)
    ratio = offline / upper
    require(2*offline > 3*upper, 'strict separation')
    require(ratio > Fraction(1505,1000), 'rounded separation')
    print('switch: B=400*380^1599, K=20^1600; 1600 main events and one terminal')
    print('offline: every event and terminal drain checked; maximum live cohort count:',
          largest_live_cohort_count)
    print('online: 1600 triangular lag rows; target coefficient:', target,
          '; sum of tail multipliers:', tail_multipliers)
    print('exact comparison: 2*offline > 3*online upper; in fact ratio > 1.505')


if __name__ == '__main__':
    verify()
