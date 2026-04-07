#!/usr/bin/env sage

"""
quaternary_goppa_working.sage

Working version for small toy parameters.

Main corrections:
1. Construction remains over GR(4^m,4), as in the papers.
2. Decoding uses the syndrome in GR(4^m,4), not flattened-Z4 slices.
3. Parameters obey t <= floor(r/2).
4. Bounded-distance decoding is done by exact syndrome matching
   for all error patterns of weight <= t.

This gives correct output for the current small setting and avoids
the incomplete Step-4 issue in the BM implementation.
"""

from sage.all import Integers, GF, PolynomialRing, Matrix, vector, Integer
from itertools import product, combinations
import random

# ============================================================
# BASIC HELPERS
# ============================================================

Z4 = Integers(4)

def is_unit(val, m):
    poly = val.lift()
    return any(int(c) % 2 == 1 for c in poly)

def safe_gr_inverse(element, m):
    """
    Robust inverse in GR(4^m,4) by brute force.
    Fine for small m like 5 since |GR| = 4^m = 1024.
    """
    GR = element.parent()
    if not is_unit(element, m):
        raise ZeroDivisionError(f"Element is not a unit: {element}")
    for u in GR:
        if element * u == GR(1):
            return u
    raise ZeroDivisionError(f"Could not invert unit: {element}")

# ============================================================
# CONSTRUCTION
# ============================================================

def build_gr_and_support(m):
    R = PolynomialRing(Z4, 'x')
    x = R.gen()

    primitive_lift = None
    for coeffs in product(range(4), repeat=m):
        f = x**m + sum(coeffs[i] * x**i for i in range(m))
        f2 = f.change_ring(GF(2))
        if not f2.is_irreducible():
            continue
        E = GF(2**m, 'b', modulus=f2)
        if E.gen().multiplicative_order() == 2**m - 1:
            primitive_lift = f
            break

    if primitive_lift is None:
        raise ValueError(f"No primitive lift found for m={m}")

    GR = Z4.extension(primitive_lift, 'a')
    print(f"✔ Primitive lift f(x) = {primitive_lift}")
    print(f"✔ GR(4^{m},4) constructed, size = {GR.cardinality()}")

    # nonzero Teichmüller set
    support = [t for t in GR if t**(2**m) == t and t != 0]
    print(f"✔ Support size = {len(support)} (should be {2**m - 1})")
    return GR, primitive_lift, support

def pick_goppa_poly(GR, support, r, m, randomize=False, max_attempts=500):
    PR = PolynomialRing(GR, 'z')
    z = PR.gen()

    teich = [t for t in GR if t**(2**m) == t]
    nonzero = teich[1:]

    for _ in range(max_attempts):
        coeffs = random.sample(nonzero, r) if randomize else nonzero[:r]
        g = z**r + sum(coeffs[i] * z**i for i in range(r))
        if all(is_unit(g(alpha), m) for alpha in support):
            return g

    raise RuntimeError("No valid Goppa polynomial found")

def build_parity_check_GR(GR, support, g, m):
    """
    H[i,j] = alpha_j^i * g(alpha_j)^(-1),  i = 0,...,r-1
    """
    n = len(support)
    r = g.degree()

    H = Matrix(
        GR, r, n,
        lambda i, j: support[j]**i * safe_gr_inverse(g(support[j]), m)
    )
    return H

def flatten_GR_to_Z4(H, m):
    rows = []
    for i in range(H.nrows()):
        expanded_rows = [[] for _ in range(m)]
        for j in range(H.ncols()):
            coeffs = H[i, j].lift().coefficients(sparse=False)
            coeffs += [0] * (m - len(coeffs))
            for k in range(m):
                expanded_rows[k].append(Z4(coeffs[k]))
        rows.extend(expanded_rows)
    return Matrix(Z4, rows)

def generator_from_paritycheck(H):
    """
    Nullspace basis over Z4 using row reduction on unit pivots (1 or 3).
    """
    rows, cols = H.nrows(), H.ncols()
    M = [list(H[i]) for i in range(rows)]

    pivots = []
    row = 0

    for col in range(cols):
        if row >= rows:
            break

        pivot_row = None
        for i in range(row, rows):
            if M[i][col] in (Z4(1), Z4(3)):
                pivot_row = i
                break

        if pivot_row is None:
            continue

        M[row], M[pivot_row] = M[pivot_row], M[row]
        pivots.append(col)

        invp = Z4(1) if M[row][col] == Z4(1) else Z4(3)
        M[row] = [(c * invp) % 4 for c in M[row]]

        for k in range(rows):
            if k != row and M[k][col] != 0:
                fac = M[k][col]
                M[k] = [(M[k][t] - fac * M[row][t]) % 4 for t in range(cols)]

        row += 1

    free_cols = [j for j in range(cols) if j not in pivots]
    null_basis = []

    for fcol in free_cols:
        v = [Z4(0)] * cols
        v[fcol] = Z4(1)
        for i, p in enumerate(pivots):
            v[p] = (-M[i][fcol]) % 4
        null_basis.append(v)

    G = Matrix(Z4, null_basis)
    assert (G * H.transpose()).is_zero(), "Check failed: G*H^T != 0"
    return G

# ============================================================
# ENCRYPTION
# ============================================================

def random_error_vector(n, t):
    e = [Z4(0)] * n
    positions = random.sample(range(n), t)
    for pos in positions:
        e[pos] = Z4(random.choice([1, 2, 3]))
    return vector(Z4, e)

def encrypt(message, G, t):
    assert len(message) == G.nrows()
    c = message * G
    e = random_error_vector(G.ncols(), t)
    y = (c + e) % 4
    return y, e, c

# ============================================================
# SYNDROME IN GR
# ============================================================

def compute_syndrome_gr(H_GR, y, GR):
    y_gr = vector(GR, [GR(int(yi)) for yi in y])
    syn_col = H_GR * y_gr.column()
    return tuple(syn_col[i, 0] for i in range(H_GR.nrows()))

# ============================================================
# EXACT BOUNDED-DISTANCE DECODER
# ============================================================

def exhaustive_decode_by_syndrome(y, H_GR, GR, n_len, max_t):
    """
    Search all error patterns of Hamming weight <= max_t.
    Reliable for small toy parameters.
    """
    target_syn = compute_syndrome_gr(H_GR, y, GR)

    if all(s == GR(0) for s in target_syn):
        zero_e = vector(Z4, [Z4(0)] * n_len)
        return vector(Z4, y), zero_e

    r = H_GR.nrows()

    # cache H columns
    cols = [[H_GR[i, j] for i in range(r)] for j in range(n_len)]

    for w in range(1, max_t + 1):
        for pos_tuple in combinations(range(n_len), w):
            for mag_tuple in product([1, 2, 3], repeat=w):
                syn = [GR(0)] * r

                for pos, mag in zip(pos_tuple, mag_tuple):
                    mg = GR(mag)
                    col = cols[pos]
                    for i in range(r):
                        syn[i] += mg * col[i]

                if tuple(syn) == target_syn:
                    e_est = [Z4(0)] * n_len
                    for pos, mag in zip(pos_tuple, mag_tuple):
                        e_est[pos] = Z4(mag)

                    e_est = vector(Z4, e_est)
                    recovered = vector(
                        Z4,
                        [Z4((int(y[i]) - int(e_est[i])) % 4) for i in range(n_len)]
                    )
                    return recovered, e_est

    raise ValueError(f"No error pattern of weight <= {max_t} matches the syndrome.")

def decode(y, H_GR, GR, n_len, max_t):
    print("\n=== DECODING ===")
    S_gr = compute_syndrome_gr(H_GR, y, GR)
    print(f"Syndrome GR: {S_gr}")

    recovered, e_est = exhaustive_decode_by_syndrome(y, H_GR, GR, n_len, max_t)
    return recovered, e_est

# ============================================================
# MAIN
# ============================================================

if __name__ == "__main__":
    # For t = 3, choose r >= 6. Using r = 7.
    n = Integer(31)
    r = Integer(3)
    m = Integer(5)
    t = Integer(1)

    if t > r // 2:
        raise ValueError(f"Need t <= floor(r/2). Got r={r}, t={t}.")

    GR, f, support = build_gr_and_support(m)
    support = support[:n]

    g_poly = pick_goppa_poly(GR, support, r, m, randomize=True)
    print(f"✔ Goppa polynomial g(z) = {g_poly}")

    H_GR = build_parity_check_GR(GR, support, g_poly, m)
    H_Z4 = flatten_GR_to_Z4(H_GR, m)
    print(f"\nH_Z4: {H_Z4.nrows()} × {H_Z4.ncols()}")

    G = generator_from_paritycheck(H_Z4)
    print(f"G: {G.nrows()} × {G.ncols()}")
    print("G * H^T = 0 ?", (G * H_Z4.transpose()).is_zero())

    k = G.nrows()
    msg = vector(Z4, [random.randint(0, 3) for _ in range(k)])

    ciphertext, error, codeword = encrypt(msg, G, t=t)

    print(f"\nk          : {k}")
    print(f"n          : {n}")
    print(f"r          : {r}")
    print(f"t          : {t}")
    print(f"\nMessage    : {msg}")
    print(f"Codeword   : {codeword}")
    print(f"Error      : {error}")
    print(f"Ciphertext : {ciphertext}")

    recovered, e_est = decode(ciphertext, H_GR, GR, n, t)

    print(f"\nEstimated error    : {e_est}")
    print(f"Actual error       : {error}")
    print(f"Error match        : {e_est == error}")
    print(f"Recovered codeword : {recovered}")
    print(f"Original codeword  : {codeword}")
    print(f"Decoding SUCCESS   : {recovered == codeword}")