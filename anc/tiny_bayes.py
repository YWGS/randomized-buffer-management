
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations, product


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def average(values):
    return Fraction(sum(values), len(values))


def active_ports(world, t):
    return tuple(t <= last for last in world)


class BatchPlanner:

    def __init__(self, capacity, horizon, labels, prefer_large):
        self.capacity = capacity
        self.horizon = horizon
        self.labels = labels
        self.empty = (0,) * labels
        states = sorted((q for q in product(range(capacity + 1), repeat=labels)
                         if sum(q) <= capacity), reverse=prefer_large)
        self.outcomes = {
            q: (sum(x > 0 for x in q), tuple(max(0, x - 1) for x in q))
            for q in states
        }

        @lru_cache(maxsize=None)
        def observable_blocks(t, worlds):
            partition = defaultdict(list)
            for world in worlds:
                partition[active_ports(world, t)].append(world)
            return tuple((active, tuple(block)) for active, block in partition.items())

        @lru_cache(maxsize=None)
        def legal(carry, active):
            return tuple(q for q in states if all(
                live or chosen <= retained for chosen, retained, live in zip(q, carry, active)
            ))

        @lru_cache(maxsize=None)
        def choose(t, carry, block, active):
            best_value = -1
            best_inventory = None
            for q in legal(carry, active):
                delivered, remaining = self.outcomes[q]
                value = delivered + before(t + 1, remaining, block)
                if value > best_value:
                    best_value = value
                    best_inventory = q
            return best_value, best_inventory

        @lru_cache(maxsize=None)
        def before(t, carry, worlds):
            if t == self.horizon:
                return Fraction(0)
            weighted = sum(len(block) * choose(t, carry, block, active)[0]
                           for active, block in observable_blocks(t, worlds))
            return Fraction(weighted, len(worlds))

        self.before = before
        self.choose = choose
        self.observable_blocks = observable_blocks

    def play(self, world, worlds):
        carry = self.empty
        support = worlds
        history = []
        for t in range(self.horizon):
            observation = active_ports(world, t)
            children = dict(self.observable_blocks(t, support))
            support = children[observation]
            _, chosen = self.choose(t, carry, support, observation)
            history.append((support, chosen))
            _, carry = self.outcomes[chosen]
        require(carry == self.empty, "online queues not empty after drain")
        return history


def sequential_offline(capacity, world, horizon, port_order):
    empty = (0,) * len(world)
    current = {empty: 0}
    for t in range(horizon):
        for port in port_order:
            if t > world[port]:
                continue
            for _ in range(capacity):
                updated = current.copy()  
                for stock, score in current.items():
                    if sum(stock) < capacity:
                        nxt = list(stock)
                        nxt[port] += 1
                        target = tuple(nxt)
                        updated[target] = max(updated.get(target, -1), score)
                    else:
                        for evicted, count in enumerate(stock):
                            if not count or port == evicted:
                                continue
                            nxt = list(stock)
                            nxt[evicted] -= 1
                            nxt[port] += 1
                            target = tuple(nxt)
                            updated[target] = max(updated.get(target, -1), score)
                current = updated
        next_slot = {}
        for stock, score in current.items():
            require(sum(stock) <= capacity, "sequential capacity violation")
            service = sum(count > 0 for count in stock)
            target = tuple(max(0, count - 1) for count in stock)
            next_slot[target] = max(next_slot.get(target, -1), score + service)
        current = next_slot
    require(set(current) == {empty}, "sequential queues not empty after drain")
    return current[empty]


def audit_inventory(planner, worlds, dates, opt):
    sizes = [worlds[0].count(date) for date in dates]
    all_gains = []
    realized_old = [[] for _ in dates]
    online_scores = []
    conditional = defaultdict(list)
    for world in worlds:
        path = planner.play(world, worlds)
        groups = [tuple(i for i, d in enumerate(world) if d == date) for date in dates]
        gains = [sum(sum(stock[i] > 0 for i in group) for _, stock in path[date:])
                 for date, group in zip(dates, groups)]
        online_scores.append(sum(sum(x > 0 for x in stock) for _, stock in path))
        all_gains.append(gains)
        for event, date in enumerate(dates):
            support, q = path[date]
            active = tuple(i for i, d in enumerate(world) if date <= d)
            group = groups[event]
            stock = sum(q[i] for i in group)
            require(gains[event] <= stock, "last-group service exceeds its actual stock")
            conditional[event, support].append((active, group, stock, q))
            previous_stock = 0
            pathwise_residuals = []
            for j in range(event):
                actual = sum(q[i] for i in groups[j])
                residual = max(0, gains[j] - sizes[j] * (date - dates[j]))
                require(actual >= residual, "earlier group's realized residual exceeds stock")
                previous_stock += actual
                pathwise_residuals.append(residual)
            realized_old[event].append(pathwise_residuals)
            require(previous_stock + sum(q[i] for i in active) == sum(q) <= planner.capacity,
                    "current and expired inventories do not partition the buffer")

    for (event, support), states in conditional.items():
        active, _, _, inventory = states[0]
        require(len(states) == len(support), "incorrect observable history multiplicity")
        require(all(a == active and q == inventory for a, _, _, q in states),
                "policy distinguishes worlds with the same arrival prefix")
        subsets = defaultdict(int)
        for _, group, _, _ in states:
            subsets[group] += 1
        require(set(subsets) == set(combinations(active, sizes[event]))
                and len(set(subsets.values())) == 1, "fresh group not uniformly hidden")
        current_stock = sum(inventory[i] for i in active)
        expected_dying_stock = average([stock for _, _, stock, _ in states])
        require(len(active) * expected_dying_stock == sizes[event] * current_stock,
                "conditional hidden-group stock identity failed")

    require(average(online_scores) == opt, "replayed payoff disagrees with Bellman value")
    gain = [average(column) for column in zip(*all_gains)]
    rows = []
    positive_lags = 0
    strict_jensen = 0
    for i, t in enumerate(dates):
        receivers = sum(sizes[i:])
        price = Fraction(receivers, sizes[i]) * gain[i]
        for j in range(i):
            term = max(0, gain[j] - sizes[j] * (t - dates[j]))
            mean_pathwise = average([terms[j] for terms in realized_old[i]])
            require(term <= mean_pathwise, "positive-part Jensen inequality failed")
            positive_lags += term > 0
            strict_jensen += term < mean_pathwise
            price += term
        require(price <= planner.capacity, "expected nonlinear inventory bound failed")
        rows.append(price)
    return tuple(rows), len(conditional), positive_lags, strict_jensen


def verify(capacity, ends, expected=None):
    dates = tuple(sorted(set(ends)))
    worlds = tuple(sorted(set(permutations(ends))))
    horizon = max(ends) + 1 + capacity
    n = len(ends)
    planner = BatchPlanner(capacity, horizon, n, prefer_large=False)
    online = planner.before(0, planner.empty, worlds)
    all_rows = []
    positive_lags = 0
    strict_jensen = 0
    fibers = None
    for prefer_large in (False, True):
        other = BatchPlanner(capacity, horizon, n, True) if prefer_large else planner
        value = other.before(0, other.empty, worlds)
        require(value == online, "optimal value depends on tie convention")
        rows, fibers, positive, strict = audit_inventory(other, worlds, dates, online)
        all_rows.extend(rows)
        positive_lags += positive
        strict_jensen += strict
    offline_results = []
    for world in worlds:
        clairvoyant_batch = planner.before(0, planner.empty, (world,))
        sorted_arrivals = sequential_offline(capacity, world, horizon, range(n))
        reversed_arrivals = sequential_offline(capacity, world, horizon, range(n - 1, -1, -1))
        require(clairvoyant_batch == sorted_arrivals == reversed_arrivals,
                "batch and sequential clairvoyant optima disagree")
        offline_results.append(sorted_arrivals)
    offline = average(offline_results)
    require(online <= offline, "online optimum exceeds clairvoyant optimum")
    if (capacity, ends) == (5, (0, 2, 3)):
        require(strict_jensen > 0, "strict Jensen regression no longer exercised")
    if expected is not None:
        require((online, offline) == expected, "published two-label illustration disagrees")
    print(f"B={capacity} expiry={ends} worlds={len(worlds)} event_histories={fibers} "
          f"online={online} offline={offline} max_inventory_lhs={max(all_rows)} "
          f"positive_lag_terms={positive_lags} strict_jensen_terms={strict_jensen}")


if __name__ == "__main__":
    cases = [(2, (0,)), (3, (0, 2)), (4, (0, 1, 3)), (5, (0, 2, 3)), (6, (0, 1, 3)),
             (4, (0, 0, 1, 1)), (3, (0, 1, 1, 3)), (5, (0, 1, 2, 4))]
    for b, last in cases:
        reference = (Fraction(13, 2), Fraction(7)) if (b, last) == (3, (0, 2)) else None
        verify(b, last, reference)
    print("PASS: both online tie conventions, every event inequality, and both sequential orders.")
