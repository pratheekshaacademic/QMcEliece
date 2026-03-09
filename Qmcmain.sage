from sage.all import Matrix, Integers, GF, PolynomialRing, vector, Integer
from itertools import product
import random

# ------------------------------------------------
# ✅ REQUIRED HELPER FUNCTIONS (FULLY CORRECTED)
# ------------------------------------------------
def is_unit(val, m):
    """
    In GR(4^m,4), an element is a unit iff its reduction mod 2 is nonzero.
    """
    poly = val.lift()
    return any(int(c) % 2 == 1 for c in poly)

def safe_gr_inverse(element):
    """
    Computes the inverse of a unit in GR(4^m, 4) using the Extended Euclidean 
    Algorithm (xgcd) on the polynomial lifts, resolving the NotImplementedError.
    """
    GR = element.parent()
    modulus_f = GR.modulus()
    element_poly = element.lift()
    
    # xgcd returns (gcd, a, b) such that gcd = a*modulus_f + b*element_poly
    g_gcd, a, b = modulus_f.xgcd(element_poly)

    Z4 = Integers(4)
    # Get the inverse of the constant term of the gcd in Z4
    g_const = g_gcd.coefficients()[0]
    inv_g_in_Z4 = Z4(g_const)**(-1) 
    
    # The inverse element is the result of (b * inv_g_in_Z4) in the ring
    inv_poly = b * inv_g_in_Z4
    
    return GR(inv_poly)

# ------------------------------------------------
# Step 1–3: Build GR and Teichmüller support
# ------------------------------------------------
def build_gr_and_support(m):
    Z4 = Integers(4)
    R = PolynomialRing(Z4, 'x'); x = R.gen()

    # Find primitive lift f(x)
    for coeffs in product(range(4), repeat=m):
        f = x**m + sum(coeffs[i]*x**i for i in range(m))
        f2 = f.change_ring(GF(2))
        if not f2.is_irreducible():
            continue
        E = GF(2**m, 'b', modulus=f2)
        if E.gen().multiplicative_order() == 2**m - 1:
            print(f"✔ Primitive lift f(x) = {f}")
            break
    else:
        raise ValueError(f"No primitive lift found for m={m}")

    GR = Z4.extension(f, 'a')
    print(f"✔ GR(4^{m},4) constructed, size={GR.cardinality()}")

    # Teichmüller support
    support = [t for t in GR if t**(2**m) == t and t != 0]
    print(f"✔ Support size = {len(support)} (should be {2**m - 1})")

    return GR, f, support

# ------------------------------------------------
# Step 4: Pick Goppa polynomial
# ------------------------------------------------
def pick_goppa_poly(GR, support, r, m, randomize=False, max_attempts=500):
    PR = PolynomialRing(GR, 'z'); z = PR.gen()
    Teich = [t for t in GR if t**(2**m) == t]
    nonzero = Teich[1:]

    for _ in range(max_attempts):
        coeffs = random.sample(nonzero, r) if randomize else nonzero[:r]
        g = z**r + sum(coeffs[i]*z**i for i in range(r))
        if all(is_unit(g(alpha), m) for alpha in support):
            return g

    raise RuntimeError("No valid Goppa polynomial found")

# ------------------------------------------------
# Step 5: Build parity-check matrix H over GR
# ------------------------------------------------
def build_parity_check_GR(GR, support, g, m):
    n = len(support)
    r = g.degree()
    order = 2**m - 1

    def inv_t(t):    # inverse in Teichmüller set
        return t**(order-1)

    H = Matrix(GR, r, n,
               lambda i, j: support[j]**i * inv_t(g(support[j])))
    return H


def flatten_GR_to_Z4(H, m):
    """
    Expand an r×n matrix over GR(4^m,4) into an (r*m)×n matrix over Z4.
    """
    Z4 = Integers(4)
    rows = []
    for i in range(H.nrows()):
        # expand each entry into length-m coefficient vector
        expanded_rows = [[] for _ in range(m)]
        for j in range(H.ncols()):
            coeffs = H[i,j].lift().coefficients(sparse=False)
            coeffs = coeffs + [0]*(m - len(coeffs))    # pad to length m
            for k in range(m):
                expanded_rows[k].append(Z4(coeffs[k]))
        rows.extend(expanded_rows)
    return Matrix(Z4, rows)

#------------------------------------------------------------------------------
# Generator MATRIX CONSTRUCTION FROM H
#-----------------------------------------------------------------------------
Z4 = Integers(4)

def generator_from_paritycheck(H):
    """
    Compute generator matrix G over Z4 such that G*H^T = 0 mod 4.
    """
    rows, cols = H.nrows(), H.ncols()
    M = [list(H[i]) for i in range(rows)]

    pivots, row = [], 0
    for col in range(cols):
        if row >= rows:
            break
        # find a pivot that is a unit (1 or 3)
        for i in range(row, rows):
            if M[i][col] in (Z4(1), Z4(3)):
                M[row], M[i] = M[i], M[row]
                pivots.append(col)
                invp = 1 if M[row][col] == 1 else 3
                M[row] = [(c * invp) % 4 for c in M[row]]
                # eliminate
                for k in range(rows):
                    if k != row and M[k][col] != 0:
                        fac = M[k][col]
                        M[k] = [(M[k][t] - fac*M[row][t]) % 4 for t in range(cols)]
                row += 1
                break

    # free variables = non-pivot columns
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

#-----------------------------------------------------------------
# ENCRYPT
#-----------------------------------------------------------------
def random_error_vector(n, t):
    """
    Generate a random error vector of length n over Z4
    with Lee weight approximately t.
    """
    e = [Z4(0)] * n
    positions = random.sample(range(n), t)
    for pos in positions:
        e[pos] = Z4(random.choice([1, 2, 3]))    # nonzero error
    return vector(Z4, e)

def encrypt(message, G, t):
    """
    Encrypt a message using generator matrix G and error weight t.
    """
    assert len(message) == G.nrows(), "Message length must match rows of G"
    c = message * G            # codeword
    e = random_error_vector(G.ncols(), t)
    y = (c + e) % 4            # ciphertext
    return y, e, c

#-----------------------------------------------------------
# SYNDROME CALCULATION
#=============================================================
def compute_syndrome_GR(H_GR, y_z4):
    """
    Computes syndrome s = y * H^T over GR(4^m, 4) using H_GR.
    """
    GR = H_GR.base_ring()
    y_gr = vector(GR, [GR(c) for c in y_z4])
    s = y_gr * H_GR.transpose()
    return list(s)

#----------------------------------------------------------------
# ✅ DECODING STEP 1: MODIFIED BERLEKAMP-MASSEY (FIXED)
#---------------------------------------------------------------
def modified_berlekamp_massey_GR(S, m):
    """
    Modified Berlekamp–Massey algorithm over GR(4^m, 4).
    FIXED: Uses safe_gr_inverse and array indexing [i].
    """
    GR = S[0].parent()
    PR = PolynomialRing(GR, 'x'); x = PR.gen()
    r = len(S)

    Lambda = PR([GR(1)])
    B = PR([GR(1)])
    L = 0
    m_shift = 1 
    d_m = GR(1)

    for t in range(r):
        # 1. Compute discrepancy d_t
        d_t = GR(0)
        for i in range(L + 1):
            if t - i >= 0:
                d_t += Lambda[i] * S[t - i]
        
        if d_t == GR(0):
            B = B * x
            continue

        # Check if d_m is a unit for safe division
        if is_unit(d_m, m):
            y = d_t * safe_gr_inverse(d_m)
            Lambda_new = Lambda - y * B * x**m_shift
        else:
            B = B * x
            continue
        
        # Check for length update condition
        if 2 * L <= t:
            L_new = t + 1 - L
            m_shift = 1
            B = Lambda
            L = L_new
            d_m = d_t
        else:
            m_shift += 1
            
        Lambda = Lambda_new

    return Lambda, L

#--------------------------------------------------------------------
# ✅ DECODING STEP 2: ERROR LOCATION (FIXED)
#---------------------------------------------------------------------

def find_error_locations_GR(sigma, support, m):
    """
    Finds error locations using the Ring-Chien Search.
    FIXED: Uses safe_gr_inverse.
    """
    GR = sigma.base_ring()
    X = []

    def is_zero_divisor(val):
        return val != GR(0) and not is_unit(val, m)

    for alpha in support:
        try:
            # Alpha is guaranteed to be a unit (Teichmüller element)
            alpha_inv = safe_gr_inverse(alpha)
            eval_val = sigma(alpha_inv)
        except ZeroDivisionError:
            continue

        # Error Location Condition: $\sigma(\alpha^{-1})$ must be a zero divisor
        if is_zero_divisor(eval_val):
            X.append(alpha)
            
    return X


def compute_error_magnitudes_fornay_GR(S, sigma, X, g_poly, m, support):
    """
    ✅ DECODING STEP 3: Computes error magnitudes using the ring-adapted Forney formula.
    FIXED: Uses safe_gr_inverse and array indexing [i].
    """
    GR = sigma.base_ring()
    nu = sigma.degree()
    
    support_map = {alpha: j for j, alpha in enumerate(support)}
    e = [GR(0)] * len(support)

    for x_j in X:
        j = support_map[x_j]
        
        # 1. Calculate coefficients $\sigma_{j,i}$ 
        sigma_coeffs = [GR(1)] * nu
        for i in range(1, nu):
            coeff = sigma[i] + x_j * sigma_coeffs[i-1]
            sigma_coeffs[i] = coeff

        # 2. Numerator N_j (Error Evaluator term)
        N_j = GR(0)
        for l in range(nu):
            if nu - 1 - l < len(S):
                N_j += sigma_coeffs[l] * S[nu - 1 - l]

        # 3. Goppa Factor E_j (g(x_j)^-1)
        E_j = safe_gr_inverse(g_poly(x_j))
            
        # 4. Denominator Factor D_j_term (Derivative term)
        D_j_term = GR(0)
        for l in range(nu):
            D_j_term += sigma_coeffs[l] * x_j**(nu - 1 - l)

        # 5. Final Division: y_j = N_j * (E_j * D_j_term)^-1
        full_denominator = E_j * D_j_term
        
        if is_unit(full_denominator, m): 
            y_j = N_j * safe_gr_inverse(full_denominator)
            e[j] = y_j
        else:
            e[j] = GR(0)
            
    return vector(GR, e)

# ------------------------------------------------
# MAIN EXECUTION BLOCK
# ------------------------------------------------
if __name__ == "__main__":
    
    n, r, m = Integer(7), Integer(2), Integer(5)
    t_max = r // 2 # Theoretical error correction capability is 1 for r=3
    Z4 = Integers(4)
    
    # ------------------ SETUP ------------------
    GR, f, support = build_gr_and_support(m)
    support = support[:n]
    g_poly = pick_goppa_poly(GR, support, r, m, randomize=True)
    
    H_GR = build_parity_check_GR(GR, support, g_poly, m)
    H_Z4 = flatten_GR_to_Z4(H_GR, m)
    G = generator_from_paritycheck(H_Z4)
    k = G.nrows()

    # ------------------ ENCRYPTION ------------------
    msg = vector(Z4, [random.randint(0,3) for _ in range(k)])
    t_errors = 1 # Using t=1, as t_max=1 for r=3
    
    ciphertext, error_z4, codeword = encrypt(msg, G, t=t_errors)
    
    # Calculate Syndrome s over the GR ring
    syndrome_gr = compute_syndrome_GR(H_GR, ciphertext)
    
    print("\n------------------ DECODING START ------------------")
    print(f"Original Error vector e: {error_z4}")
    print(f"Syndrome (GR elements): {syndrome_gr}")

    # ------------------ DECODING STEP 1: MBM ------------------
    Lambda, nu = modified_berlekamp_massey_GR(syndrome_gr, m)
    print("\n[Step 1: MBM]")
    print(f"Locator $\Lambda(x)$ over GR: {Lambda}") 
    if nu > t_max:
        print(f"DECODING FAILURE: Detected $\\nu = {nu}$ errors, exceeds $t_{{max}} = {t_max}$")
    
    # ------------------ DECODING STEP 2: ERROR LOCATION ------------------
    X = find_error_locations_GR(Lambda, support, m)
    print("\n[Step 2: Error Location]")
    print(f"Found {len(X)} error locations (GR elements).")
    
    # ------------------ DECODING STEP 3: ERROR MAGNITUDE ------------------
    error_gr = compute_error_magnitudes_fornay_GR(syndrome_gr, Lambda, X, g_poly, m, support)
    
    # Extract the Z4 coefficient (index 0) from the GR error vector
    error_corrected_z4 = vector(Z4, [e.lift().coefficients(sparse=False)[0] if e != GR(0) else Z4(0) for e in error_gr])
    
    corrected_codeword = ciphertext - error_corrected_z4
    
    print("\n[Step 3: Error Magnitude & Correction]")
    print(f"Reconstructed Error Vector (Z4): {error_corrected_z4}")
    print(f"Original Error Vector (Z4): {error_z4}")
    
    print(f"\nSUCCESS CHECK: Reconstructed error matches original? -> {error_corrected_z4 == error_z4}")
    print(f"SUCCESS CHECK: Final codeword matches original? -> {corrected_codeword == codeword}")
