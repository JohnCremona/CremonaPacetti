#
# For K a number field, S a finite set of primes of K and G in
# {C2,C3,S3} we find all extensions of K with Galois group G and
# unramified outside S.
#
# The main inefficiency here is that when P does not contain all
# primes dividing 2 we do more work to be certain that each
# K(\sqrt{a}) is unramified outside S.  THis could be done more
# effieicntly with more work.  SImilarly fpr pure cubic extensions
# when S does not contain all primes above 3.
#

from sage.all import ProjectiveSpace, GF, prod, polygen
proof.number_field(False)

# Over QQ we can do x.is_S_unit(S) when x is an element but not an
# ideal; over other number fields only ideals have the method, not
# elements!

def is_S_unit(a, S):
    r"""Returns True iff a is an S-unit where a is in Q or in a number
    field K and S is a list of primes of K.
    """
    #print("a = {}".format(a))
    K = a.parent()
    #print("K = {}".format(K))
    if K in [ZZ,QQ]:
        return QQ(a).is_S_unit(S)
    try:
        return a.is_S_unit(S)
    except AttributeError:
        return K.ideal(a).is_S_unit(S)

def unramified_outside_S(L,S):
    r"""Return True if the extension L is unramified over its base field K
    outside the set S of primes of K.
    """
    return is_S_unit(L.relative_discriminant(),S)

def selmer_group_projective(K,S,p):
    r"""Return iterator over the nontrivial elements of K(S,p) up to
    scaling for p prime, i.e. only yield one generator of each
    subgroup of order p.  This could easily be moved into
    K.selmer_group_iterator(S,p) as an option.
    """
    KSgens = K.selmer_group(S=S, m=p)
    for ev in ProjectiveSpace(GF(p),len(KSgens)-1):
        yield prod([q ** e for q, e in zip(KSgens, list(ev))], K.one())

############## C2 (quadratic extensions) ###############################

def C2_extensions(K,S):
    r"""Return all quadratic extensions of K unramified outside S.

    These all have the form \(K(\sqrt{a})\) for \(a\) in \(K(S,2)\)
    but it S does not contain all primes dividing 2 some of these may
    be ramified at primes dividing 2 not in S so we need to do an
    additional check.

    We return polynomials defining the extension rather than the extensions themselves.
    """
    x = polygen(K)
    # if some primes above 2 are not in S then a further check is required
    test = lambda a: True if is_S_unit(K(2),S) else lambda a: unramified_outside_S(K.extension(x**2-a,'t2'))
    return [x**2-a for a in K.selmer_group_iterator(S,2) if not a.is_square() and test(a)]

############## C3 (cyclic cubic extensions) ###############################

def C3_extensions(K,S, verbose=False):
    r"""Return all C3 extensions of K unramified outside S.

    If K contains the cube roots of unity, these all have the form
    \(K(\root[3]{a})\) for \(a\) in \(K(S,3)\) but it S does not
    contain all primes dividing 3 some of these may be ramified at
    primes dividing 3 not in S so we need to do an additional
    check. In the general case we need to work harder.

    We return polynomials defining the extension rather than the extensions themselves.
    """
    x = polygen(K)
    if verbose:
        print("finding C3 extensions over {} unramified outside {}".format(K,S))

    if K(-3).is_square(): ## K contains cube roots of unity
        test = lambda a: True if is_S_unit(K(3),S) else lambda a: unramified_outside_S(K.extension(x**3-a,'t3'))
        # use K(S,3), omitting trivial element and only including one element per subgroup:
        return [x**3-a for a in selmer_group_projective(K,S,3) if test(a)]

    # now K does not contain the cube roots of unity.  We adjoin them.
    # See AK's thesis Algorithm 3 (page 45)

    K3 = K.extension(x**2+x+1,'z3')
    S3 = sum([K3.primes_above(P) for P in S],[])
    if verbose:
        print("finding alphas")
    alphas = [a for a in selmer_group_projective(K3,S3,3) if a.norm(K).is_nth_power(3)]
    if verbose:
        print("found {} alphas".format(len(alphas)))
    try:
        traces = [a.trace(K) for a in alphas]
    except TypeError:
        traces = [a.trace() for a in alphas]
    betas = [a.norm(K).nth_root(3) for a in alphas]
    polys = [x**3-3*b*x-t for b,t in zip(betas, traces)]
    fields = [K.extension(f,'t3') for f in polys]
    # (debug) check the fields are not isomorphic (relative to K):
    # assert all([not any([fields[i].is_isomorphic_relative(fields[j])
    #                     for j in range(i)]) for i in range(len(fields))])
    return [f for f,L in zip(polys,fields) if unramified_outside_S(L,S)]

############## S3 (non-cyclic cubic extensions) ###############################

def S3_extensions_with_resolvent(K,S,M, verbose=False):
    r"""Return all S3 extensions of K unramified outside S with quadratic
    resolvent subfield M (which must be unramified outside S too).

    We return a list of cubics h with Galois group S3 and resoplvent field M.
    """
    if verbose:
        print("finding S3 extensions over {} unramified outside {} with quadratic resolvent {}".format(K,S,M))
    g = [e for e in M.automorphisms() if e(M.gen()) != M.gen()][0]  #the generator of Gal(M/K)
    SM = sum([M.primes_above(p) for p in S],[])
    if verbose:
        print("first find C3 extensions of {}".format(M))
    cubics = C3_extensions(M,SM) #all the cubic extensions of M unramified outside SM
    if verbose:
        print("{} cubics found".format(len(cubics)))

    # Now from these cubics L/M/K we must pick out those which are Galois with group S3 not C6:
    Mx = PolynomialRing(M,'xM')
    Kx = PolynomialRing(K,'x')
    def test(f):
        if verbose:
            print("testing {}".format(f))
        fbar = Mx([g(c) for c in f.coefficients(sparse=False)])
        if f==fbar:
            if verbose:
                print("easy case as this f is in K[x]")
            h = Kx([c[0] for c in f.coefficients(sparse=False)])
            if h.discriminant().is_square():
                return False
            return h
        # both f splits over L since L/K is C3
        # if fbar does not split over L then L/K is not Galois:
        L = f.base_ring().extension(f,'c')
        fbar_roots = fbar.roots(L, multiplicities=False)
        if len(fbar_roots)==0:
            return False
        # now L/K is Galois.
        f_roots = f.roots(L, multiplicities=False)
        y = f_roots[0]+fbar_roots[0]
        if y==0:
            y = f_roots[0]+fbar_roots[1]
        if verbose:
            print("f, fbar distinct.  Using y={} with minpoly {}".format(y,y.minpoly()))
        # h is the min poly of y, which is in K[x] when S3 NB if h is
        # not in K[x] then certailny C6; if h is in K[x] it may be C6
        # and we have to check the discriminant later.
        coeffs = y.minpoly().coefficients(sparse=False)
        if any(c[1]!=0 for c in coeffs):
            return False
        h = Kx([c[0] for c in coeffs])
        if verbose:
            print("h = {}".format(h))
        if h.discriminant().is_square():
            if verbose:
                print("...discarding as discriminant is square")
            return False
        if not h.is_irreducible():
            if True:#verbose:
                print("...!!!!!!!!!!!!!!!discarding as reducible")
            return False
        if verbose:
            print("...returning as valid")
        return h

    if verbose:
        print("testing each cubic extension to see if it is S3 over the base")
    polys = [test(f) for f in cubics] # includes some False entries
    polys = [h for h in polys if h]
    # check results are valid and distinct:
    bad_h = [h for h in polys if not h.is_irreducible()]
    if bad_h:
        print("error in S3_extensions_with_resolvent(), M={}, returning reducible polynomial(s) {}!".format(M, bad_h))
    if verbose:
        print("polys (before final test): {}".format(polys))
    fields_and_embeddings = [h.splitting_field('a',map=True) for h in polys]
    fields = [L.relativize(e,'a') for L,e in fields_and_embeddings]
    if verbose:
        print("fields (before final test): {}".format(fields))
    pols_and_fields = [hL for hL in zip(polys,fields) if unramified_outside_S(hL[1],S)]
    pols   = [h for h,L in pols_and_fields]
    fields = [L for h,L in pols_and_fields]
    if verbose:
        print("polys  (after final test): {}".format(pols))
        print("fields (after final test): {}".format(fields))
    return pols

def S3_extensions(K,S, verbose=False):
    r"""Return all S3 extensions of K unramified outside S.

    We return a list of pairs (h,L) where h is the cubic and L its splitting field.
    """
    if verbose:
        print("finding S3 extensions over {} unramified outside {}".format(K,S))
    C2_extns = [K.extension(f, 't2') for f in C2_extensions(K,S)]
    return sum([S3_extensions_with_resolvent(K,S,M,verbose) for M in C2_extns],[])

############## C3 & S3 extensions ###############################

def C3S3_extensions(K,S, verbose=False):
    r"""Return all C3 and S3 extensions of K unramified outside S.
    """
    return C3_extensions(K,S,verbose) + S3_extensions(K,S,verbose)

############## V4 (biquadratic extensions) ###############################

def V4_extensions(K,S, verbose=False):
    r"""Return all V4 extensions of K unramified outside S.  The
    polynomials returned are irreducible.
    """
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
    g = [e for e in M.automorphisms() if e(M.gen()) != M.gen()][0]  #the generator of Gal(M/K)
    SM = sum([M.primes_above(P) for P in S],[])
    DM = M.defining_polynomial().discriminant()
    x = polygen(K)
    # if some primes above 2 are not in S then a further check is required
    test = lambda a: True if is_S_unit(M(2),SM) else lambda a: unramified_outside_S(M.extension(x**2-a,'t2'),SM)
    alphas = [a for a in M.selmer_group_iterator(SM,2) if not a.is_square() and (DM*a.relative_norm()).is_square() and test(a)]
    return [x**4-a.trace()*x**2+a.norm(K) for a in alphas]

def C4_extensions(K,S, verbose=False):
    r"""Return all C4 extensions of K unramified outside S.  The
    polynomials returned are irreducible.
    """
    if verbose:
        print("finding C4 extensions of {} unramified outside {}".format(K,S))
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
    alphas = [a for a in M.selmer_group_iterator(SM,2) if not a.is_square() and a.norm().is_square()]
    def make_quartic(a):
        # a is in the cubic extension M/K and has square norm, so has
        # minpoly of the form x^3-p*x^2+q*x-r^2.
        r2, q, p, one = list(a.minpoly())
        p = -p
        r = (-r2).sqrt()
        x = polygen(r)
        return (x**2-p)**2-8*r*x-4*q

    return [make_quartic(a) for a in alphas]

def A4_extensions(K,S, verbose=False):
    r"""Return all A4 extensions of K unramified outside S.

    Returns quartic polynomials with Galois group A4.
    """
    if verbose:
        print("finding A4 extensions of {} unramified outside {}".format(K,S))

    cubics = [K.extension(f,'t3') for f in C3_extensions(K,S)]
    return sum([A4_extensions_with_resolvent(K,S,M, verbose) for M in cubics], [])

def S4_extensions(K,S, verbose=False):
    r"""Return all S4 extensions of K unramified outside S.

    Returns quartic polynomials with Galois group S4.
    """
    if verbose:
        print("finding S4 extensions of {} unramified outside {}".format(K,S))

    cubics = [K.extension(f,'t3') for f in S3_extensions(K,S)]
    return sum([A4_extensions_with_resolvent(K,S,M, verbose) for M in cubics], [])
