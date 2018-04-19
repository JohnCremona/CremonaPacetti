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

from sage.all import ProjectiveSpace, GF, prod, polygen, proof, ZZ, QQ, PolynomialRing, NumberField

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

def unramified_outside_S(L,S, p=None):
    r"""Return True if the extension L is unramified over its base field K
    outside the set S of primes of K.  If p is not None assume that
    only primes dividing p need to be tested.
    """
    # This one-liner works but is slow
    # return is_S_unit(L.relative_discriminant(),S)
    debug = False
    if debug:
        print("testing ramification of {}".format(L))
    f = L.defining_polynomial()
    d = f.discriminant()
    K = f.base_ring()
    if p is not None:
        Kp = K(p)
        bads = [P for P in K.primes_above(p) if d.valuation(P)>0]
        if not bads:
            if debug:
                print("OK: no bad primes in disc")
            return True
        if any(d.valuation(P)%2==1 for P in bads):
            if debug:
                print("NO: disc has odd valn at some bad primes in disc")
            return False
        if K.absolute_discriminant()%p!=0:
            if debug:
                print("computing abs disc of {}-maximal order".format(p))
            ram = ZZ(p).divides(L.maximal_order([p]).absolute_discriminant())
            if debug:
                print("...done, returning {}".format(not ram))
            return not ram
        if debug:
            print("p={} but quick methods failed to give an answer".format(p))

    if K==QQ:
        D = d
    else:
        D = K.ideal(d)
    for P in S:
        for _ in range(D.valuation(P)):
            D /= P
    # now D is the prime-to-S part of disc(f)
    if debug:
        print("Prime-to-S part of disc = {} with norm {}".format(D,D.absolute_norm()))
    try:
        bads = D.prime_factors()
    except AttributeError:
        bads = D.support()
    if debug:
        print("bads = {}".format(bads))
    if not bads:
        if debug:
            print("OK: no bad primes in disc")
        return True
    if any(d.valuation(P)%2==1 for P in bads):
        if debug:
            print("NO: disc has odd valn at some bad primes in disc")
        return False
    # Now d is divisible by one or more primes not in S, to even
    # powers, and we must work harder to see if L is ramified at these
    # primes.
    if debug:
        print("final check of {} bad primes in disc: {}".format(len(bads), bads))
    ram = any(any(Q.relative_ramification_index()>1 for Q in L.primes_above(P)) for P in bads)
    if debug:
        print("NO" if ram else "OK")
    return not ram

def selmer_group_projective(K,S,p):
    r"""Return iterator over the nontrivial elements of K(S,p) up to
    scaling for p prime, i.e. only yield one generator of each
    subgroup of order p.  This could easily be moved into
    K.selmer_group_iterator(S,p) as an option.
    """
    KSgens = K.selmer_group(S=S, m=p)
    #print("projective Selmer group has dimension {}".format(len(KSgens)))
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
    if is_S_unit(K(2),S):
        test = lambda a: True
    else:
        test = lambda a: unramified_outside_S(K.extension(x**2-a,'t2'), S, 2)
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
    from KSp import pSelmerGroup
    x = polygen(K)
    if verbose:
        print("finding C3 extensions over {} unramified outside {}".format(K,S))

    if K(-3).is_square(): ## K contains cube roots of unity
        if is_S_unit(K(3),S): # primes dividing 3 are in S -- easy case
            test = lambda a: True
        else:
            test = lambda a: unramified_outside_S(K.extension(x**3-a,'t3'), S, 3)
        # use K(S,3), omitting trivial element and only including one element per subgroup:
        return [x**3-a for a in selmer_group_projective(K,S,3) if test(a)]

    # now K does not contain the cube roots of unity.  We adjoin them.
    # See AK's thesis Algorithm 3 (page 45)

    if verbose:
        print("finding alphas")

    # Find downstairs Selmer group:
    KS3, KS3_gens, from_KS3, to_KS3 = pSelmerGroup(K,S,ZZ(3))
    if verbose:
        print("Downstairs 3-Selmer group has dimension {}".format(KS3.dimension()))
    # Find upstairs Selmer group:
    K3 = K.extension(x**2+x+1,'z3')
    nm = lambda p: p if p in ZZ else p.absolute_norm()
    S3 = sum([K3.primes_above(P) for P in S if nm(P)%3!=2],[])
    K3S3, K3S3_gens, from_K3S3, to_K3S3 = pSelmerGroup(K3,S3,ZZ(3))
    if verbose:
        print("Upstairs 3-Selmer group has dimension {}".format(K3S3.dimension()))

    # construct norm map on these:
    N = K3S3.hom([to_KS3(from_K3S3(v).norm(K)) for v in K3S3.basis()], KS3)
    ker = N.kernel()
    if False:#verbose:
        print("Norm map: {}".format(N))
        print("kernel: {}".format(ker))
    Pker = ProjectiveSpace(ker.dimension()-1,ker.base())
    alphas = [from_K3S3(ker.linear_combination_of_basis(list(v))) for v in Pker]
    #alphas = [a for a in selmer_group_projective(K3,S3,3) if a.norm(K).is_nth_power(3)]
    if verbose:
        print("found {} alphas".format(len(alphas)))
        #print(alphas)
    try:
        traces = [a.trace(K) for a in alphas]
    except TypeError:
        traces = [a.trace() for a in alphas]
    if verbose: print("computed {} traces".format(len(traces)))
    betas = [a.norm(K).nth_root(3) for a in alphas]
    if verbose: print("computed {} betas".format(len(betas)))
    polys = [x**3-3*b*x-t for b,t in zip(betas, traces)]
    if verbose: print("computed {} polys".format(len(polys)))
    # NB because of the additional extension, these may be ramified at
    # primes above 3, not all of which are necessarily in S, so we
    # must check.
    debug = False
    check_3 = not is_S_unit(K(3),S)
    if debug or check_3:
        fields = [K.extension(f,'t3') for f in polys]
        if verbose: print("computed fields, checking ramification")
    if K == QQ:
        if not (debug or check_3):
            fields = [K.extension(f,'t3') for f in polys]

        fields = [L.optimized_representation()[0] for L in fields]
        polys = [L.defining_polynomial() for L in fields]

    # (debug) check the fields are not isomorphic (relative to K):
    if debug:
        if K==QQ:
            assert all([not any([fields[i].is_isomorphic(fields[j])
                                 for j in range(i)]) for i in range(len(fields))])
        else:
            assert all([not any([fields[i].is_isomorphic_relative(fields[j])
                                 for j in range(i)]) for i in range(len(fields))])
    # the polys we have are already guaranteed to be unramified
    # outside S, by construction, except possibly at primes dividing 3
    # not in S.
    if check_3:
        polys_and_fields = zip(polys,fields)
        if verbose:
            print("Final check of primes dividing 3 not in S")
        polys_and_fields = [fL for fL in polys_and_fields if unramified_outside_S(fL[1],S,3)]
        if verbose:
            print("After final check, {} polys remain".format(len(polys_and_fields)))
        polys  = [f for f,L in polys_and_fields]
        fields = [L for f,L in polys_and_fields]
    if debug:
        if not polys == [f for f,L in zip(polys,fields) if unramified_outside_S(L,S)]:
            print("Problem: relative discriminants are {}".format([L.relative_discriminant().factor() for L in fields]))
        else:
            if verbose: print("computed unramified polys OK")
    return polys

############## S3 (non-cyclic cubic extensions) ###############################

def S3_extensions_with_resolvent(K,S,M, verbose=False):
    r"""Return all S3 extensions of K unramified outside S with quadratic
    resolvent subfield M (which must be unramified outside S too).

    We return a list of cubics h with Galois group S3 and resolvent field M.
    """
    if verbose:
        print("finding S3 extensions over {} unramified outside {} with quadratic resolvent {}".format(K,S,M))
    g = [e for e in M.automorphisms() if e(M.gen()) != M.gen()][0]  #the generator of Gal(M/K)
    SM = sum([M.primes_above(p) for p in S],[])
    # if we add in primes above 3 here then the C3 extension search
    # need not bother about checking ramification above 3.  We'll do
    # that later where it will be quick as not so relative.
    for P in M.primes_above(3):
        if not P in SM:
            SM.append(P)

    if verbose:
        print("first find C3 extensions of {}".format(M))
    cubics = C3_extensions(M,SM,verbose=verbose) #all the cubic extensions of M unramified outside SM
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
        # not in K[x] then certainly C6; if h is in K[x] it may be C6
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
    pols_and_fields = [hL for hL in zip(polys,fields)]
    debug = False
    pols_and_fields = [hL for hL in pols_and_fields if unramified_outside_S(hL[1],S)]

    pols   = [h for h,L in pols_and_fields]
    fields = [L for h,L in pols_and_fields]
    if K == QQ:
        pols = [NumberField(pol,'a').optimized_representation()[0].defining_polynomial() for pol in pols]
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
    SM = sum([M.primes_above(P) for P in S],[])
    DM = M.defining_polynomial().discriminant()
    x = polygen(K)
    # if some primes above 2 are not in S then a further check is required
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
