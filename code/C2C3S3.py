#
# For K a number field, S a finite set of primes of K and G in
# {C2;C3,S3} we find all extensions of K with Galois group G and
# unramified outside S.  In the case of S3 it is possible to specify
# the quadratic resolvent.
#
# The main inefficiency here is that when P does not contain all
# primes dividing 2 we do more work to be certain that each
# K(\sqrt{a}) is unramified outside S.  This could be done more
# efficiently with more work.  Similarly for pure cubic extensions
# when S does not contain all primes above 3.
#
# For the cubics we use Kummer theory, following Cohen's book and
# Angelos Koutsiasnas's thesis for some details.  Where we use Kummer
# theory to construct cyclic extensions we could alternatively use
# Class Field Theory, and we expect to write code for that once
# https://trac.sagemath.org/ticket/15829 is finished.
#
#

from sage.all import ProjectiveSpace, polygen, proof, ZZ, QQ, PolynomialRing, NumberField

# The following line means that class groups, etc, are computed
# non-rigorously (assuming GRH) which makes everything run faster.

proof.number_field(False)

# Over QQ we can do x.is_S_unit(S) when x is an element but not an
# ideal; over other number fields only ideals have the method, not
# elements!

def is_S_unit(a, S):
    r"""Returns True iff a is an S-unit where a is in Q or in a number
    field K and S is a list of primes of K.

    INPUT:

    - ``a`` (integer, rational or number field element or ideal) --
    any integer or rational number, or number field element, or
    fractional ideal.

    - ``S`` (list) -- list of prime numbers or prime ideals

    OUTPUT:

    (boolean) ``True`` if and only if ``a`` is an ``S``-unit.
  """
    K = a.parent()
    # rationals have an is_S_unit method:
    if K in [ZZ,QQ]:
        return QQ(a).is_S_unit(S)
    # fractional ideals also have such a method:
    try:
        return a.is_S_unit(S)
    except AttributeError:
        return K.ideal(a).is_S_unit(S)

def unramified_outside_S(L,S, p=None, debug=False):
    r"""Test whether ``L`` is unramified over its base outside ``S``.

    INPUT:

    - ``L`` (relative number field) -- a relative number field with base field `K`.

    - ``S`` (list) -- a list pf primes of `K`.

    - ``p`` (prime or ``None`` (default)) -- if not ``None``, a prime number.

    - ``debug`` (boolean (default ``False``)) -- debugging flag.

    OUTPUT:

    (boolean) ``True`` if and only if 'L/K' is unramified outside `S`.
    If `p` is not ``None`` only test primes dividing `p`.
    """
    # This one-liner works but is slow
    # return is_S_unit(L.relative_discriminant(),S)
    if debug:
        print("testing ramification of {}".format(L))
    f = L.defining_polynomial()
    d = f.discriminant()
    K = f.base_ring()
    if p is not None:
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

############## C2 (quadratic extensions) ###############################

def C2_extensions(K,S):
    r"""Return all quadratic extensions of K unramified outside S.

    INPUT:

    - ``K`` (number field) -- a number field, or ``QQ``.

    - ``S`` (list) -- a list of prime ideals in ``K``, or primes.

    OUTPUT:

    (list) A list of monic polynomials of the form `x^2-a` with `a\in
    K` defining all quadratic extensions of `K` unramified outside
    `S`.

    .. note::

       These all have the form `K(\sqrt{a})` for `a\in K(S,2)', but if
       `S` does not contain all primes dividing 2 then some of these
       may be ramified at primes dividing 2 not in `S`, so we need to
       do an additional check.
    """
    x = polygen(K)
    # if some primes above 2 are not in S then a further check is required
    if is_S_unit(K(2),S):
        test = lambda a: True
    else:
        test = lambda a: unramified_outside_S(K.extension(x**2-a,'t2'), S, 2)
    return [x**2-a for a in K.selmer_group_iterator(S,2) if not a.is_square() and test(a)]

############## C3 (cyclic cubic extensions) ###############################

def C3_extensions(K,S, verbose=False, debug=False):
    r"""Return all `C_3` extensions of ``K`` unramified outside ``S``.

    INPUT:

    - ``K`` (number field) -- a number field, or ``QQ``.

    - ``S`` (list) -- a list of prime ideals in ``K``, or primes.

    - ``verbose`` (boolean, default ``False``) -- verbosity flag.
    OUTPUT:

    - ``debug`` (boolean, default ``False``) -- debugging flag.
    OUTPUT:

    (list) A list of polynomials of degree 3 in `K[x]` defining all
    Galois cubic extensions of `K` unramified outside `S`.

    .. note::

       If `K` contains the cube roots of unity, these all have the
       form `K(\root[3]{a})` for `a\in (K(S,3)`, but if `S` does not
       contain all primes dividing 3 some of these may be ramified at
       primes dividing 3 not in `S` so we need to do an additional
       check. In the general case we need to work harder: we work over
       `K(\zeta_3)` and then descend.
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
        # use K(S,3), omitting trivial element and only including one of a, a^-1:
        from KSp import selmer_group_projective
        return [x**3-a for a in selmer_group_projective(K,S,3) if test(a)]

    # now K does not contain the cube roots of unity.  We adjoin them.
    # See Angelos Koutsianas's thesis Algorithm 3 (page 45)

    if verbose:
        print("finding alphas")

    # Find downstairs Selmer group and maps:
    KS3, KS3_gens, from_KS3, to_KS3 = pSelmerGroup(K,S,ZZ(3))
    if verbose:
        print("Downstairs 3-Selmer group has dimension {}".format(KS3.dimension()))

    # Find upstairs Selmer group and maps:
    K3 = K.extension(x**2+x+1,'z3')
    nm = lambda p: p if p in ZZ else p.absolute_norm()
    S3 = sum([K3.primes_above(P) for P in S if nm(P)%3!=2],[])
    K3S3, K3S3_gens, from_K3S3, to_K3S3 = pSelmerGroup(K3,S3,ZZ(3))
    if verbose:
        print("Upstairs 3-Selmer group has dimension {}".format(K3S3.dimension()))

    # construct norm map from K3S3 to KS3 and find its kernel:
    N = K3S3.hom([to_KS3(from_K3S3(v).norm(K)) for v in K3S3.basis()], KS3)
    ker = N.kernel()
    Pker = ProjectiveSpace(ker.dimension()-1,ker.base())
    alphas = [from_K3S3(ker.linear_combination_of_basis(list(v))) for v in Pker]

    # The alphas are the elements of this kernel
    if verbose:
        print("found {} alphas".format(len(alphas)))
        #print(alphas)

    # Compute the trace of each alpha:
    try:
        traces = [a.trace(K) for a in alphas]
    except TypeError:
        traces = [a.trace() for a in alphas]
    if verbose: print("computed {} traces".format(len(traces)))

    # Compute the betas, cube roots of each alpha's norm:
    betas = [a.norm(K).nth_root(3) for a in alphas]
    if verbose: print("computed {} betas".format(len(betas)))

    # Form the polynomials
    polys = [x**3-3*b*x-t for b,t in zip(betas, traces)]
    if verbose: print("computed {} polys".format(len(polys)))

    # NB because of the additional extension, these may be ramified at
    # primes above 3, not all of which are necessarily in S, so we
    # must check.  If S already contained all primes dividing 3 this
    # would already be the desired list.

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
    r"""Return all `S_3` extensions of ``K`` unramified outside ``S`` with
    quadratic resolvent field ``M``.

    INPUT:

    - ``K`` (number field) -- a number field, or ``QQ``.

    - ``S`` (list) -- a list of prime ideals in ``K``, or primes.

    - ``M`` (number field) -- a relative number field over ``K``
      unramified outside ``S``.

    - ``verbose`` (boolean, default ``False``) -- verbosity flag.

    OUTPUT:

    (list) A list of monic polynomials of degree 3 in `K[x]` defining
    all non-Galois cubic extensions of `K` unramified outside `S` for
    which the quadratic subfield of the splitting field is `M`.

    """
    if verbose:
        print("finding S3 extensions over {} unramified outside {} with quadratic resolvent {}".format(K,S,M))

    # compute the generator of Gal(M/K)
    g = [e for e in M.automorphisms() if e(M.gen()) != M.gen()][0]

    # find the primes of M above those in S
    SM = sum([M.primes_above(p) for p in S],[])

    # if we add in primes above 3 here then the C3 extension search
    # need not bother about checking ramification above 3, so will be
    # faster.  We'll do that later where it will be quick as not so
    # relative.
    for P in M.primes_above(3):
        if not P in SM:
            SM.append(P)

    # Find all C3 extensions of M unramified outside SM:
    if verbose:
        print("first find C3 extensions of {}".format(M))
    cubics = C3_extensions(M,SM,verbose=verbose) #all the cubic extensions of M unramified outside SM
    if verbose:
        print("{} cubics found".format(len(cubics)))

    # Now from these cubics L/M/K we must pick out those which are
    # Galois and have group S3 (not C6):
    Mx = PolynomialRing(M,'xM')
    Kx = PolynomialRing(K,'x')

    # test function for cubics in M[x].  If they define S3 Galois
    # extensions of K then we return a cubic over K with the same
    # splitting field, otherwise we return False.

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
            if True: # this should not happen
                print("...!!!!!!!!!!!!!!!discarding as reducible")
            return False
        if verbose:
            print("...returning as valid")
        return h

    # Using the test function we select those cubics which define S3 extensions over K

    if verbose:
        print("testing each cubic extension to see if it is S3 over the base")
    polys = [test(f) for f in cubics] # includes some False entries
    polys = [h for h in polys if h]

    # Now polys is a list of cubics over K with the correct quadratic resolvent.

    # We check these are valid and define distinct extensions:
    bad_h = [h for h in polys if not h.is_irreducible()]
    if bad_h:
        print("error in S3_extensions_with_resolvent(), M={}, returning reducible polynomial(s) {}!".format(M, bad_h))
    if verbose:
        print("polys (before final test): {}".format(polys))

    # For each poly in the list we construct its splitting field:
    fields_and_embeddings = [h.splitting_field('a',map=True) for h in polys]
    fields = [L.relativize(e,'a') for L,e in fields_and_embeddings]
    if verbose:
        print("fields (before final test): {}".format(fields))
    pols_and_fields = [hL for hL in zip(polys,fields)]
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
    r"""Return all `C_3` and  `S_3` extensions of ``K`` unramified outside ``S``.

    INPUT:

    - ``K`` (number field) -- a number field, or ``QQ``.

    - ``S`` (list) -- a list of prime ideals in ``K``, or primes.

    - ``verbose`` (boolean, default ``False``) -- verbosity flag.

    OUTPUT:

    (list) A list of monic polynomials of degree 3 in `K[x]` defining
    all Galois or non-Galois cubic extensions of `K` unramified outside `S`.
    """
    return C3_extensions(K,S,verbose) + S3_extensions(K,S,verbose)

