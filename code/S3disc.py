# Function to determine the quadratic subfield cut out by the mod-2
# reduction of an irreducible 2-adic Galois representation, either
# using the traces modulo 4 (ideas developed with John Voight) or just
# mod 2 information.

from sage.all import ZZ, GF, PolynomialRing, Matrix, vector, prod

def is_P_inert(a, P):
    F = GF(P) if P in ZZ else P.residue_field()
    return int(len(PolynomialRing(a.parent(), 'x')([-a,0,1]).roots(F))==0)

def get_disc(K, S, BB, mod4=False, verbose=False):
    r"""Compute the discriminant (mod squares) of the splitting field of
    an irreducible GL(2,2)-representation.

    INPUT:

    - K is a number field
    - S is a finite set of primes of K, not dividing 2
    - BB is a mod-2 "Black Box" dict with keys primes P not in S and
      values (t,n) where the characteristic polynomial of Frobenius is
      X^2-t*X+n

    - mod4: if True then we have traces and determinants mod 4 (will
      all be 1), otherwise we only have them mod 2.

    OUTPUT:

    Either D, a nonzero element of K, which is the discriminant of the
    quadratic subfield of the splitting field of BB if the image is
    S3, or 1 if the image is C3; or 0 if no primes with odd trace were
    processed.

    In the former case, we will have proved that the representation is
    irreducible and found the discriminant (mod squares) of its
    splitting field.  We can use this to find the splitting field
    itself.  In the latter case, we expect that the representatioin is
    reducible, but will need to do more work to prove this.

    ALGORITHM:

    If BB[P]=(t,n), let r = (1-t+n) = det(Frob_P-I).  There are three
    cases, according to the conjugacy class of the image of the
    Frobenius at P:

    1. if \rho(Frob_P) = I mod 2,         then t%2 == 0 and r%4 == 0;
    2. if \rho(Frob_P) mod 2 has order 2, then t%2 == 0 and r%2 == 0;
    3. if \rho(Frob_P) mod 2 has order 3, then t%2 == 1 and r%2 == 1.

    Note that Case 3 is possible if and only if the representation is
    irreducible, and will occur for a set of primes of density 1/3
    (for S3 image) or 2/3 (for C3 image).

    For P which are split in the discriminant field, \rho(Frob_P) mod
    2 has order 1 or 3, so r%4 = 0, 1, or 3; while if P is inert then
    \rho(Frob_P) mod 2 has order 2, so r%4 = 0 or 2.

    Hence:

    - if t%2==1 then P is split (image has order 3);
    -  otherwise, if r%4==2 then P is inert (image has order 2);
    -             else we cannot tell (image may have order 1 or 2).

    If the image is C3 then using only primes with odd trace is
    sufficient to saturate the matrix and D=1 will be returned.  This
    only uses the traces mod 2. Justification: for all candidate D
    not 1 there are infinitely many -- density 1/2 -- primes which are
    inert, so all D not 1 can be eliminated.

    If the image is S3 with discriminant D, then primes with odd trace
    will saturate up to codimension 1 (justification as above: all
    other D except 1 can be eliminated), at which point D will be
    (represented by) the unique mod-2 vector orthogonal to every row
    of the matrix M, which we can then find by computing the right
    kernel of M.  This would still only use traces mod 2.  However, if
    we do have mod-4 information in the BB values, then we may also
    use primes of even trace (with the trace and determinant values
    mod 4), and can usually saturate the matrix and then use the test
    vector to find D; but this can fail, for example with elliptic
    curve '162a1' where the discriminant is -1 (mod squares), so we
    have even trace for all p=3 (mod 4) but for all these we have
    1+p-ap=0 (mod 4).

    Hence the code must allow for M to only saturate up to codimension
    1, even in the irreducible case.  Nevertheless, we do expect that,
    for irreducible representations, we will encounter many primes
    with odd trace, and hence prove irreducubility, unless the Black
    Box has very little data in it.
    """
    # Make sure primes above 2 are all in S
    if K.degree()==1:
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
    V = [] # test vector, entries will be v
    reducible = True
    for P, aP in BB.items():
        if P in S:
            continue
        aP, nP = BB[P]
        v = 0
        aPodd = aP%2==1
        if aPodd: # then irreducible and P splits
            reducible = False
        else:
            if not mod4:
                continue
            if (1-aP+nP)%4==2: # then P inert
                v = 1
            else: # 1-aP+nP = 0 (mod 4), ambiguous
                if verbose:
                    print("Skipping P={} since (aP,nP)=({},{})=({},{}) mod 4".format(P,aP,nP,aP%4,nP%4))
                continue
        if verbose:
            if mod4:
                print("Using P={} with (aP,nP)=({},{})=({},{}) mod 4, so v={}".format(P,aP,nP,aP%4,nP%4, v))
            else:
                print("Using P={} with aP={} mod 2".format(P,aP))

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

        if r == rKS2:
            break

    if r < rKS2:
        if verbose and mod4:
            print("Unable to saturate matrix using {} primes!".format(len(BB)))
        if reducible:
            # we have not proved reducible but have no evidence of irreducible
            return 0
        if r==rKS2-1:
            exponents = [int(e) for e in M.right_kernel().basis()[0]]
            disc = prod((a for e,a in zip(exponents,KS2) if e), K(1))
            if verbose:
                print("Exponent vector = {}".format(exponents))
                print("discriminant = {}".format(disc))
            return disc
        print("Irreducible but saturation codimension >1: need to provide aP for more primes")
        return 0

    if verbose:
        print("Final test set of primes is {}".format(T))
        print("Test vector = {}".format(V))
    V = vector(GF(2), V)
    Minv = M.inverse()
    exponents = [int(e) for e in Minv*V]
    if verbose:
        print("Exponent vector = {}".format(exponents))
    disc = prod((a for e,a in zip(exponents,KS2) if e), K(1))

    # check:
    assert V == vector(GF(2), [is_P_inert(disc,P) for P in T])
    return disc

# Test functions

# Create BB from an elliptic curve:

def BBfromEC(E, maxn=100):
    maxn = ZZ(maxn) # else error over QQ
    K = E.base_field()
    N = E.conductor()
    S = (2*N).support()
    nm = lambda P: P
    if K.degree()>1:
        nm = lambda P: P.norm()
    tr = lambda P: E.reduction(P).trace_of_frobenius()
    BB = dict([(P,(tr(P),nm(P))) for P in K.primes_of_bounded_norm_iter(maxn) if P not in S])
    return BB

## Test that the D we find is the discriminant of E up to squares,
## either with mod2 information only, or with mod4 information

def testE(E, maxn=100, mod4=True, verbose=False):
    K = E.base_field()
    N = E.conductor()
    S = (2*N).support()
    discE = E.discriminant()
    if verbose:
        print("Testing E = {} = {}".format(E.label(), E.ainvs()))
        print("disc(E) = {}".format(discE))
    BB = BBfromEC(E, maxn)
    D = get_disc(K, S, BB, mod4, verbose=verbose)
    if D:
        if verbose:
            print("found D = {}".format(D), end="")
        ok = (D*discE).is_square()
        if verbose:
            if ok:
                print(" -- OK")
            else:
                print(" -- ********** wrong ************")
        return ok
    else:
        ok = E.two_torsion_rank()>0
        if verbose:
            print("unable to determine discriminant, probably reducible")
        if verbose:
            if ok:
                print(" -- OK")
            else:
                print(" -- ********** wrong ************")
        return ok


def test_range(N1,N2, maxn=100, mod4=True, verbose=False):
    from sage.all import cremona_curves
    for E in cremona_curves(range(N1,N2+1)):
        print(E.label(), end=": ")
        assert testE(E, maxn, mod4, verbose)
        print("OK")
