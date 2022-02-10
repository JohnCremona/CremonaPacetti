# Function to determine the quadratic subfield cut out by the mod-2
# reduction of a 2-adic Galois representation, using the traces modulo
# 4 (as suggested by John Voight)

def is_P_inert(a, P):
    F = GF(P) if P in ZZ else P.residue_field()
    return int(len(PolynomialRing(a.parent(), 'x')([-a,0,1]).roots(F))==0)

def get_disc(K, S, BB, verbose=False):
    """
    K is a number field
    S is a finite set of primes of K
    BB is a "Black Box" dict with keys primes P not in S and values traces of P
    """
    # Make sure primes above 2 are all in S
    if K is QQ:
        S2 = [] if 2 in S else [2]
    else:
        S2 = [P for P in K.primes_above(2) if P not in S]
    if S2 and verbose:
        print("adding primes {} dividing 2 into S".format(S2))
    S2 += S

    # Find the K-Selmer group (generators only needed)
    KS2 = K.selmer_generators(S, 2, False) # False means no proof
    rKS2 = len(KS2)
    if verbose:
        print("K(S,2) has {} generators: {}".format(rKS2, KS2))

    M = Matrix(GF(2), 0, rKS2)
    r = 0
    T = [] # test primes
    V = [] # test vector

    for P, aP in BB.items():
        aP = BB[P]
        nP = P if K is QQ else P.norm()
        v = 0 if aP%2==1 else 1 if (aP+nP-1)%4==0 else -1
        if v==-1:
            if verbose:
                print("Skipping P={} since (aP,nP)=({},{})=({},{}) mod 4".format(P,aP,nP,aP%4,nP%4))
            continue
        if verbose:
            print("Using P={} with (aP,nP)=({},{})=({},{}) mod 4, so v={}".format(P,aP,nP,aP%4,nP%4, v))

        row = vector([is_P_inert(a,P) for a in KS2])
        if verbose:
            print("New row is {}".format(row))
        M1 = M.stack(row)
        r1 = M1.rank()
        if r==r1:
            if verbose:
                print(" -- redundant, ignoring P")
            continue
        M = M1
        r = r1
        if verbose:
            print("*********Rank is now {}".format(r))
        T.append(P)
        V.append(v)
        if r==rKS2:
            break

    if r < rKS2:
        print("Unable to saturate matrix using {} primes!".format(len(BB)))
        return None
    if verbose:
        print("Final test set of primes is {}".format(T))
        print("Test vector = {}".format(V))
    V = vector(GF(2), V)
    Minv = M.inverse()
    exponents = [int(e) for e in Minv*V]
    if verbose:
        print("Exponent vector = {}".format(exponents))
    disc = prod(a for e,a in zip(exponents,KS2) if e)

    # check:
    col = vector(GF(2), [is_P_inert(disc,P) for P in T])
    if verbose:
        print("col = {}".format(col))
    assert col==V
    return disc

# Test functions

# Create BB from an elliptic curve:

def BBfromEC(E, maxn=300):
    maxn = ZZ(maxn) # else error over QQ
    K = E.base_field()
    N = E.conductor()
    S = (2*N).support()
    BB = dict([(P,E.reduction(P).trace_of_frobenius()) for P in K.primes_of_bounded_norm_iter(maxn) if P not in S])
    return BB

## Test that the D we find is the discriminant of E up to squares:

def testE(E, verbose=False):
    K = E.base_field()
    N = E.conductor()
    S = (2*N).support()
    BB = BBfromEC(E)
    D = get_disc(K, S, BB, verbose=verbose)
    if D:
        print("found D = {}".format(D))
        discE = E.discriminant()
        print("disc(E) = {}".format(discE))
        return (D*discE).is_square()
    else:
        print("unable to determine discriminant")
        return False

