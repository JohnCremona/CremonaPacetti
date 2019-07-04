#
# For K a number field, S a finite set of primes of K and G in
# {C4,D4,V4,A4,S4} we find all extensions of K with Galois group G and
# unramified outside S.  In the case of C4, A4, S4 it is possible to
# specify the cubic resolvent.  D4 extensions to be added later.
#

from sage.all import polygen, PolynomialRing, QQ, ZZ, Set, pari

def sagepol(paripol):
    Qx = PolynomialRing(QQ,'x')
    return Qx(str(paripol))

def polredabs(pol):
    return sagepol(pari(pol).polredabs()) if pol.base_ring()==QQ else pol
#
#
############## V4 (biquadratic extensions) ###############################

def V4_extensions_with_quadratic(K,S,M, verbose=False):
    r"""Return all V4 extensions of K unramified outside S which contain
    the quadratic extension M (also unramified outside S).  The
    polynomials returned are irreducible.
    """
    from C2C3S3 import C2_extensions
    C2s = C2_extensions(K,S)
    if M.is_relative():
        D = M.relative_discriminant()
    else:
        D = M.discriminant()

    if K==QQ:
        D=D.squarefree_part()
    ds = [f.discriminant() for f in C2s]
    if K==QQ:
        ds = [d.squarefree_part() for d in ds]
    dMs = [d*D for d in ds]
    if K==QQ:
        dMs = [d.squarefree_part() for d in dMs]
    indices = [i for i in range(len(ds)) if ds[i]!=D and dMs.index(ds[i])<i]
    ds = [ds[i] for i in indices]
    x = polygen(K)
    return [polredabs(x**4 - 2*(D+d)*x**2 + (D-d)**2) for d in ds]

def V4_extensions(K,S, verbose=False):
    r"""Return all V4 extensions of K unramified outside S.  The
    polynomials returned are irreducible.
    """
    from C2C3S3 import C2_extensions
    C2s = C2_extensions(K,S)
    ds = [f.discriminant() for f in C2s]
    if K==QQ:
        ds = [d.squarefree_part() for d in ds]
    #print("ds = {}".format(ds))
    ab_pairs = []
    all_pairs = []
    for i,a in enumerate(ds):
        for b in ds[:i]:
            if Set([a,b]) in all_pairs:
                continue
            c = a*b
            if K==QQ:
                c = c.squarefree_part()
            ab_pairs.append([a,b])
            all_pairs.append(Set([a,b]))
            all_pairs.append(Set([a,c]))
            all_pairs.append(Set([c,b]))
    #print("ab pairs = {}".format(ab_pairs))
    x = polygen(K)
    #print( [(x**4 - 2*(a+b)*x**2 + (a-b)**2) for a,b in ab_pairs])
    return [polredabs(x**4 - 2*(a+b)*x**2 + (a-b)**2) for a,b in ab_pairs]


############## C4 (cyclic quartic extensions) ###############################

def C4_extensions_with_quadratic(K,S,M, verbose=False):
    r"""Return all C4 extensions of K containing the quadratic
    extension M of K, unramified outside S.
    """
    if verbose:
        print("finding C4 extensions of {} over {} unramified outside {}".format(K,M,S))
    SM = sum([M.primes_above(P) for P in S],[])
    DM = M.defining_polynomial().discriminant()
    x = polygen(K)
    # if some primes above 2 are not in S then a further check is required
    from C2C3S3 import is_S_unit, unramified_outside_S
    if is_S_unit(M(2),SM):
        test = lambda a: True
    else:
        test = lambda a: unramified_outside_S(M.extension(polygen(M)**2-a,'t4'),SM)
    alphas = [a for a in M.selmer_group_iterator(SM,2) if not a.is_square() and (DM*a.relative_norm()).is_square() and test(a)]
    return [polredabs(x**4-a.trace(K)*x**2+a.norm(K)) for a in alphas]

def C4_extensions(K,S, verbose=False):
    r"""Return all C4 extensions of K unramified outside S.  The
    polynomials returned are irreducible.
    """
    if verbose:
        print("finding C4 extensions of {} unramified outside {}".format(K,S))
    from C2C3S3 import C2_extensions
    C2_extns = [K.extension(f, 't2') for f in C2_extensions(K,S)]
    return sum([C4_extensions_with_quadratic(K,S,M,verbose) for M in C2_extns],[])

############## D4 (dihedral quartic extensions) ###############################

def D4_extensions_with_quadratic(K,S,M, verbose=False):
    r"""Return all D4 extensions of K unramified outside S which are cyclic
    extensions of the quadratic field M, where M is also unramified
    outside S.
    """
    if verbose:
        print("finding D4 extensions of {} over {} unramified outside {}".format(K,M,S))

    SM = sum([M.primes_above(P) for P in S],[])
    sigma = M.automorphisms()[1]

    from KSp import pSelmerGroup
    MS2, MS2_gens, from_MS2, to_MS2 = pSelmerGroup(M,SM,ZZ(2))
    betas2 = [from_MS2(v) for v in MS2 if v]
    # remove conjugates (mod squares):
    conj_ind = lambda b: betas2.index(from_MS2(to_MS2(sigma(b))))
    betas = [b for i,b in enumerate(betas2) if not conj_ind(b)<i]
    # remove those whose norm is a square in M:
    norms  = [b.norm() for b in betas]
    betas = [b for b,n in zip(betas,norms) if not M(n).is_square()]
    norms  = [b.norm() for b in betas]
    traces = [b.trace() for b in betas]
    x = polygen(K)
    return [polredabs(x**4-t*x**2+n) for t,n in zip(traces,norms)]

def D4_extensions(K,S, verbose=False):
    r"""Return all D4 extensions of K unramified outside S.

    Returns quartic polynomials with Galois group D4.
    """
    if verbose:
        print("finding D4 extensions of {} unramified outside {}".format(K,S))

    from C2C3S3 import C2_extensions
    quadratics = [K.extension(f,'t2') for f in C2_extensions(K,S)]
    return sum([D4_extensions_with_quadratic(K,S,M, verbose) for M in quadratics], [])

############## A4 quartic extensions ###############################

def A4_extensions_with_resolvent(K,S,M, verbose=False):
    r"""Return all A4 extensions of K unramified outside S with cubic
    resolvent M where M is a C3 extension of K, also unramified
    outside S.

    The exact same code gives all S4-extensions whose cubic resolvent
    is the normal closure of M, when M is a non-Galois cubic.
    """
    if verbose:
        print("finding A4 extensions of {} over {} unramified outside {}".format(K,M,S))

    SM = sum([M.primes_above(P) for P in S],[])

    from KSp import pSelmerGroup
    KS2, KS2_gens, from_KS2, to_KS2 = pSelmerGroup(K,S,ZZ(2))
    #print("gens of KS2: {}".format(KS2_gens))
    MS2, MS2_gens, from_MS2, to_MS2 = pSelmerGroup(M,SM,ZZ(2))
    #print("gens of MS2: {}".format(MS2_gens))
    #print("with norms : {}".format([b.norm() for b in MS2_gens]))
    # construct norm map from MS2 to KS2 and find its kernel:
    N = MS2.hom([to_KS2(from_MS2(v).norm(K)) for v in MS2.basis()], KS2)
    #print("N={}".format(N))
    ker = N.kernel()
    #print("ker={}".format(ker))
    alphas = [from_MS2(v) for v in ker if v]
    #print("alphas = {}".format(alphas))
    #print("norms  = {}".format([alpha.norm() for alpha in alphas]))

    # In case M/K is Galois (i.e. a cyclic cubic) then the Galois
    # group acts on the alphas with no fixed points, and we only want
    # one per orbit, as otherwise we will construct the same quartic 3
    # times.  We test for this here -- despite the function's name we
    # also use this to construct S4 extensions with given cubic
    # resovent in which case M/K is not Galois and there is no
    # repetition.

    autos = M.automorphisms()
    if len(autos)==3:        # remove conjugates (mod squares):
        sigma = autos[1]
        def first_conjugate_index(a):
            sa = sigma(a)
            i = alphas.index(from_MS2(to_MS2(sa)))
            j = alphas.index(from_MS2(to_MS2(sigma(sa))))
            return min(i,j)
        alphas = [a for i,a in enumerate(alphas) if not first_conjugate_index(a)<i]

    def make_quartic(a):
        # a is in the cubic extension M/K and has square norm, so has
        # char poly of the form x^3-p*x^2+q*x-r^2.
        r2, q, p, one = list(a.charpoly())
        p = -p
        assert (-r2).is_square()
        r = (-r2).sqrt()
        x = polygen(K)
        return polredabs((x**2-p)**2-8*r*x-4*q)

    quartics = [make_quartic(a) for a in alphas]
    nq1 = len(quartics)
    #print("before testing for repeats we have {} quartics".format(nq1))
    quartics = [q for i,q in enumerate(quartics)
                if not any(K.extension(q,'t').is_isomorphic_relative(K.extension(q2,'t2'))
                           for q2 in quartics[:i])]
    nq2 = len(quartics)
    #print("after  testing for repeats we have {} quartics".format(nq2))
    if nq1!=nq2:
        print("repeats detected in A4_extensions_with_resolvent(): {} reduced to {}".format(nq1,nq2))
        print("K = {}".format(K))
        print("S = {}".format(S))
        print("M = {}".format(M))
        print("#autos = {}".format(len(autos)))
    return quartics

def A4_extensions(K,S, verbose=False):
    r"""Return all A4 extensions of K unramified outside S.

    Returns quartic polynomials with Galois group A4.
    """
    if verbose:
        print("finding A4 extensions of {} unramified outside {}".format(K,S))

    from C2C3S3 import C3_extensions
    cubics = [K.extension(f,'t3') for f in C3_extensions(K,S)]
    return sum([A4_extensions_with_resolvent(K,S,M, verbose) for M in cubics], [])

############## S4 quartic extensions ###############################

def S4_extensions_with_quadratic(K,S,M, verbose=False):
    r"""Return all S4 extensions of K unramified outside S with given quadratic subfield M.

    Returns quartic polynomials with Galois group S4.
    """
    if verbose:
        print("finding S4 extensions of {} unramified outside {}".format(K,S))

    from C2C3S3 import S3_extensions_with_resolvent
    cubics = [K.extension(f,'t3') for f in S3_extensions_with_resolvent(K,S,M)]
    return sum([A4_extensions_with_resolvent(K,S,L, verbose) for L in cubics], [])

def S4_extensions(K,S, verbose=False):
    r"""Return all S4 extensions of K unramified outside S.

    Returns quartic polynomials with Galois group S4.
    """
    if verbose:
        print("finding S4 extensions of {} unramified outside {}".format(K,S))

    from C2C3S3 import S3_extensions
    cubics = [K.extension(f,'t3') for f in S3_extensions(K,S)]
    return sum([A4_extensions_with_resolvent(K,S,M, verbose) for M in cubics], [])

############## "absolutely irreducible" quartic extensions ###############################
#
#  The subgroups whose isomorphs in PGL(2,3) are absolutely irreducible are S4, A4, D4, V4
#   (where V4 denotes the subgroup containing the prosucts of 2 transpositions)
#
def abs_irred_extensions_with_quadratic(K,S,M, verbose=False):
    return S4_extensions_with_quadratic(K,S,M) + D4_extensions_with_quadratic(K,S,M)

def abs_irred_extensions_even(K,S, verbose=False):
    return A4_extensions(K,S) + V4_extensions(K,S)

def abs_irred_extensions(K,S, verbose=False):
    return S4_extensions(K,S) + A4_extensions(K,S) + D4_extensions(K,S) + V4_extensions(K,S)

############## "irreducible" quartic extensions ###############################
#
#  The subgroups whose isomorphs in PGL(2,3) are irreducible are S4,
#   A4, D4, V4, C4, C2 (where V4 denotes the subgroup containing the
#   prosucts of 2 transpositions, and C2 is a subgroup of the form
#   <(12)(34)>.
#
#
def irred_extensions_with_quadratic(K,S,M, verbose=False):
    return S4_extensions_with_quadratic(K,S,M) +\
        D4_extensions_with_quadratic(K,S,M) +\
        C4_extensions_with_quadratic(K,S,M)

def irred_extensions_even(K,S, verbose=False):
    from C2C3S3 import C2_extensions
    return A4_extensions(K,S) + V4_extensions(K,S) + C2_extensions(K,S)

def irred_extensions(K,S, verbose=False):
    from C2C3S3 import C2_extensions
    return S4_extensions(K,S) + A4_extensions(K,S) + D4_extensions(K,S) +\
        V4_extensions(K,S) + C4_extensions(K,S) + C2_extensions(K,S)

