#!/usr/bin/env sage

"""
quaternary_goppa_andrade_refined.sage

Practical Andrade-style decoder over GR(4^m,4).

Pipeline:
  Step 1: syndrome in GR
  Step 2: modified Berlekamp–Massey in GR
  Step 3: reciprocal roots + zero-divisor candidate positions
  Step 3b: refine candidate positions by exact syndrome consistency
  Step 4: recover magnitudes in Z4 and decode

Recommended toy parameters:
    m = 6
    n = 63
    r = 7
    t = 3
"""

from sage.all import Integers, GF, PolynomialRing, Matrix, vector, Integer
from itertools import product, combinations
import random

# ============================================================
# GLOBAL
# ============================================================

Z4 = Integers(4)

# ============================================================
# BASIC HELPERS
# ============================================================

def coeff_list_ring(x, m):
    coeffs = x.lift().coefficients(sparse=False)
    return coeffs + [0] * (m - len(coeffs))

def is_unit(val, m):
    return any(int(c) % 2 == 1 for c in coeff_list_ring(val, m))

def is_zero_divisor_or_zero(val, m):
    return (val == val.parent()(0)) or (not is_unit(val, m))

def safe_gr_inverse(element, m):
    GR = element.parent()
    if not is_unit(element, m):
        raise ZeroDivisionError(f"Element is not a unit: {element}")
    for u in GR:
        if element * u == GR(1):
            return u
    raise ZeroDivisionError(f"Could not invert unit: {element}")

def reciprocal_poly(poly):
    PR = poly.parent()
    BR = PR.base_ring()
    d = poly.degree()
    cc = poly.coefficients(sparse=False)
    cc += [BR(0)] * (d + 1 - len(cc))
    return PR(list(reversed(cc[:d + 1])))

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

    if not null_basis:
        raise ValueError(
            f"Generator matrix is trivial: nullspace dimension is 0. "
            f"Choose parameters with n > rows. Here n={cols}, rows={rows}."
        )

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
# STEP 1: SYNDROME IN GR
# ============================================================

def compute_syndrome_gr(H_GR, y, GR):
    y_gr = vector(GR, [GR(int(v)) for v in y])
    syn_col = H_GR * y_gr.column()
    return [syn_col[i, 0] for i in range(H_GR.nrows())]

# ============================================================
# STEP 2: MODIFIED BERLEKAMP–MASSEY OVER GR
# ============================================================

def discrepancy_of_sigma(S, sigma, n_idx):
    cc = sigma.coefficients(sparse=False)
    ell = sigma.degree()
    d = S[n_idx]
    for i in range(1, ell + 1):
        if i < len(cc):
            d += cc[i] * S[n_idx - i]
    return sigma.parent().base_ring()(d)

def satisfies_first_m_power_sums(S, sigma, m_idx):
    ell = sigma.degree()
    if m_idx < ell:
        return True
    for n_idx in range(ell, m_idx + 1):
        if discrepancy_of_sigma(S, sigma, n_idx) != sigma.parent().base_ring()(0):
            return False
    return True

def modified_berlekamp_massey_gr(S, GR, m_ring):
    """
    Practical Andrade-style BM over GR with a search-based Step 4.
    """
    PR = PolynomialRing(GR, 'x')
    x = PR.gen()
    zero = GR(0)
    one = GR(1)

    N = len(S)
    if N == 0:
        return PR(1)

    # Initial conditions
    # sigma^(-1)=1, l_-1=0, d_-1=1
    # sigma^(0)=1,  l_0=0,  d_0=s_0
    history = [
        {'n': -1, 'sigma': PR(1), 'l': 0, 'd': one},
        {'n':  0, 'sigma': PR(1), 'l': 0, 'd': S[0]}
    ]

    current_sigma = PR(1)
    current_l = 0
    current_d = S[0]
    n = 0

    while n < N - 1:
        if current_d == zero:
            next_sigma = current_sigma
            next_l = current_l
        else:
            best = None
            best_score = None

            # Step 3
            for entry in history:
                pn, ps, pl, pd = entry['n'], entry['sigma'], entry['l'], entry['d']
                if pn > n - 1:
                    continue
                if pd == zero:
                    continue

                # find y such that d_n - y d_m = 0, i.e. y*d_m = d_n
                for y_try in GR:
                    if y_try * pd == current_d:
                        score = pn - pl
                        if best is None or score > best_score:
                            best = (pn, ps, pl, pd, y_try)
                            best_score = score
                        break

            if best is None:
                next_sigma = current_sigma
                next_l = current_l
            else:
                pn, ps, pl, pd, y_try = best
                shift = n - pn
                next_sigma = current_sigma - y_try * x**shift * ps
                next_l = max(current_l, pl + shift)

                # Step 4
                threshold = max(current_l, n + 1 - current_l)
                if next_l != threshold:
                    candidates = []

                    for entry in history:
                        pn2, ps2, pl2, pd2 = entry['n'], entry['sigma'], entry['l'], entry['d']
                        if pn2 > n - 1:
                            continue

                        if pd2 != -current_d:
                            continue

                        ps2_cc = ps2.coefficients(sparse=False)
                        sigma0 = ps2_cc[0] if ps2_cc else zero
                        if not is_zero_divisor_or_zero(sigma0, m_ring):
                            continue

                        shift2 = n - pn2
                        D = current_sigma + x**shift2 * ps2
                        lD = D.degree()

                        if threshold <= lD < next_l:
                            if satisfies_first_m_power_sums(S, ps2, pn2):
                                candidates.append((lD, pn2, D))

                    if candidates:
                        candidates.sort(key=lambda t: (t[0], t[1]))
                        next_sigma = candidates[0][2]
                        next_l = candidates[0][0]

        d_next = discrepancy_of_sigma(S, next_sigma, n + 1) if (n + 1) < N else zero
        history.append({'n': n + 1, 'sigma': next_sigma, 'l': next_l, 'd': d_next})

        current_sigma = next_sigma
        current_l = next_l
        current_d = d_next
        n += 1

    return current_sigma

# ============================================================
# STEP 3: RECIPROCAL ROOTS + ZERO-DIVISOR CANDIDATES
# ============================================================

def roots_in_gr(poly, GR):
    roots = []
    for z in GR:
        if poly(z) == GR(0):
            roots.append(z)
    return roots

def find_error_positions_gr(sigma, support, m_ring, GR):
    if sigma.degree() <= 0:
        return [], [], None

    rho = reciprocal_poly(sigma)
    roots = roots_in_gr(rho, GR)

    candidates = set()
    for z in roots:
        for j, alpha in enumerate(support):
            if is_zero_divisor_or_zero(alpha - z, m_ring):
                candidates.add(j)

    return sorted(candidates), roots, rho

# ============================================================
# STEP 3b / 4: REFINE POSITIONS AND SOLVE MAGNITUDES
# ============================================================

def solve_magnitudes_for_subset(S_gr, subset, support, g_poly, m_ring, GR):
    """
    For a chosen subset of positions, solve magnitudes in {1,2,3}
    using the syndrome equations over GR.
    """
    r = len(S_gr)
    w = len(subset)

    cols = []
    for pos in subset:
        alpha = support[pos]
        ginv = safe_gr_inverse(g_poly(alpha), m_ring)
        col = [alpha**l * ginv for l in range(r)]
        cols.append(col)

    for mags in product([1, 2, 3], repeat=w):
        syn = [GR(0)] * r
        for j in range(w):
            mj = GR(mags[j])
            for l in range(r):
                syn[l] += mj * cols[j][l]

        if syn == list(S_gr):
            return {subset[j]: Z4(mags[j]) for j in range(w)}

    return None

def refine_error_positions_and_magnitudes(S_gr, sigma, candidate_idx, support, g_poly, m_ring, GR):
    nu = sigma.degree()

    if len(candidate_idx) < nu:
        raise ValueError(f"Not enough candidate positions: need {nu}, got {len(candidate_idx)}")

    for subset in combinations(candidate_idx, nu):
        mags = solve_magnitudes_for_subset(S_gr, subset, support, g_poly, m_ring, GR)
        if mags is not None:
            return list(subset), mags

    raise ValueError(f"Could not refine candidate positions. Candidates={candidate_idx}, degree={nu}")

# ============================================================
# FULL DECODE
# ============================================================

def decode_andrade(y, H_GR, support, g_poly, m_ring, GR, n_len):
    print("\n=== DECODING (ANDRADE STYLE, REFINED) ===")

    # Step 1
    S_gr = compute_syndrome_gr(H_GR, y, GR)
    print(f"Syndrome GR        = {S_gr}")

    # Step 2
    Lambda = modified_berlekamp_massey_gr(S_gr, GR, m_ring)
    print(f"Lambda(x)          = {Lambda}  [degree {Lambda.degree()}]")

    if Lambda.degree() <= 0:
        zero_e = vector(Z4, [Z4(0)] * n_len)
        return vector(Z4, y), zero_e

    # Step 3
    candidate_idx, roots, rho = find_error_positions_gr(Lambda, support, m_ring, GR)
    print(f"Reciprocal rho(z)  = {rho}")
    print(f"Roots of rho       = {roots}")
    print(f"Candidate positions= {candidate_idx}")

    if not candidate_idx:
        raise ValueError("No candidate error positions found from reciprocal roots.")

    # Step 3b / 4
    err_idx, mags = refine_error_positions_and_magnitudes(
        S_gr, Lambda, candidate_idx, support, g_poly, m_ring, GR
    )
    print(f"Refined positions  = {err_idx}")
    print(f"Magnitudes         = {{ {', '.join(f'{j}: {int(v)}' for j, v in mags.items())} }}")

    e_est = vector(Z4, [Z4(0)] * n_len)
    for j, mag in mags.items():
        e_est[j] = mag

    recovered = vector(Z4, [Z4((int(y[i]) - int(e_est[i])) % 4) for i in range(n_len)])
    return recovered, e_est

# ============================================================
# MAIN
# ============================================================

if __name__ == "__main__":
    # Recommended parameters
    n = Integer(63)
    r = Integer(7)
    m = Integer(6)
    t = Integer(3)

    if t > r // 2:
        raise ValueError(f"Need t <= floor(r/2). Got r={r}, t={t}")

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
    print(f"m          : {m}")
    print(f"t          : {t}")
    print(f"\nMessage    : {msg}")
    print(f"Codeword   : {codeword}")
    print(f"Error      : {error}")
    print(f"Ciphertext : {ciphertext}")

    recovered, e_est = decode_andrade(ciphertext, H_GR, support, g_poly, m, GR, n)

    print(f"\nEstimated error    : {e_est}")
    print(f"Actual error       : {error}")
    print(f"Error match        : {e_est == error}")
    print(f"Recovered codeword : {recovered}")
    print(f"Original codeword  : {codeword}")
    print(f"Decoding SUCCESS   : {recovered == codeword}")