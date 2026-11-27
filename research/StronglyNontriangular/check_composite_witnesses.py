"""Check the fixed-omega(n) representation counts by unrelated exact enumerations."""

from math import gcd, isqrt


def squarefree_odd_factor_count(limit):
    least_prime = list(range(limit + 1))
    for p in range(2, isqrt(limit) + 1):
        if least_prime[p] == p:
            for t in range(p * p, limit + 1, p):
                if least_prime[t] == t:
                    least_prime[t] = p
    orders = [0] * (limit + 1)
    for t in range(3, limit + 1, 2):
        p = least_prime[t]
        u = t // p
        if u % p and (u == 1 or orders[u]):
            orders[t] = orders[u] + 1
    return orders


def check(limit=100_000):
    orders = squarefree_odd_factor_count(limit + 1)
    rows = max(orders) + 1
    triangle = [[0] * (limit + 1) for _ in range(rows)]
    divisor = [[0] * (limit + 1) for _ in range(rows)]
    for a in range(2, isqrt(2 * limit) + 1):
        for b in range(a, 2 * limit // (a + 1) + 1):
            if (a - b) % 2 == 0 or gcd(a, b) > 1:
                continue
            n = (a * b + a + b - 1) // 2
            d = (a if a % 2 == 0 else b) + 1
            if n <= limit and orders[d] > 0:
                triangle[orders[d]][n] += 1
    for d in range(3, limit + 2, 2):
        k = orders[d]
        if k:
            for n in range(2 * d - 1, limit + 1, d):
                if gcd(d - 1, 2 * n + 1) == 1:
                    divisor[k][n] += 1
    for k in range(1, rows):
        assert triangle[k] == divisor[k], k
        print(f"k={k}: {sum(divisor[k]):,} representations among "
              f"{sum(x > 0 for x in divisor[k]):,} distinct n <= {limit:,}")


if __name__ == "__main__":
    check()
