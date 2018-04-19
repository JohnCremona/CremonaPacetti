#
# For K a number field, S a finite set of primes of K and G in
# {V4,C4,A4,S4} we find all extensions of K with Galois group G and
# unramified outside S.  In the case of C4, A4, S4 it is possible to
# specify the cubic resolvent.  D4 extensions to be added later.
#

from sage.all import polygen

#
#
############## V4 (biquadratic extensions) ###############################

def V4_extensions(K,S, verbose=False):
    r"""Return all V4 extensions of K unramified outside S.  The
    polynomials returned are irreducible.
    """
    from C2C3S3 import C2_extensions
    C2s = C2_extensions(K,S)
    ab_pairs = [(C2s[i](0), C2s[j](0)) for i in range(len(C2s)) for j in range(len(C2s)) if i<j]
    x = polygen(K)
    return [x**4 + 2*(a+b)*x**2 + (a-b)**2 for a,b in ab_pairs]


############## C4 (cyclic quartic extensions) ###############################

def C4_extensions_with_resolvent(K,S,M, verbose=False):
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
        test = lambda a: unramified_outside_S(M.extension(x**2-a,'t2'),SM)
    alphas = [a for a in M.selmer_group_iterator(SM,2) if not a.is_square() and (DM*a.relative_norm()).is_square() and test(a)]
    return [x**4-a.trace()*x**2+a.norm(K) for a in alphas]

def C4_extensions(K,S, verbose=False):
    r"""Return all C4 extensions of K unramified outside S.  The
    polynomials returned are irreducible.
    """
    if verbose:
        print("finding C4 extensions of {} unramified outside {}".format(K,S))
    from C2C3S3 import C2_extensions
    C2_extns = [K.extension(f, 't2') for f in C2_extensions(K,S)]
    return sum([C4_extensions_with_resolvent(K,S,M,verbose) for M in C2_extns],[])


############## A4 (cyclic quartic extensions) ###############################

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
    alphas = [a for a in M.selmer_group_iterator(SM,2) if (not a.is_square()) and a.norm().is_square()]
    def make_quartic(a):
        # a is in the cubic extension M/K and has square norm, so has
        # char poly of the form x^3-p*x^2+q*x-r^2.
        r2, q, p, one = list(a.charpoly())
        p = -p
        r = (-r2).sqrt()
        x = polygen(K)
        return (x**2-p)**2-8*r*x-4*q

    return [make_quartic(a) for a in alphas]

def A4_extensions(K,S, verbose=False):
    r"""Return all A4 extensions of K unramified outside S.

    Returns quartic polynomials with Galois group A4.
    """
    if verbose:
        print("finding A4 extensions of {} unramified outside {}".format(K,S))

    from C2C3S3 import C3_extensions
    cubics = [K.extension(f,'t3') for f in C3_extensions(K,S)]
    return sum([A4_extensions_with_resolvent(K,S,M, verbose) for M in cubics], [])

def S4_extensions(K,S, verbose=False):
    r"""Return all S4 extensions of K unramified outside S.

    Returns quartic polynomials with Galois group S4.
    """
    if verbose:
        print("finding S4 extensions of {} unramified outside {}".format(K,S))

    from C2C3S3 import S3_extensions
    cubics = [K.extension(f,'t3') for f in S3_extensions(K,S)]
    return sum([A4_extensions_with_resolvent(K,S,M, verbose) for M in cubics], [])
