# C2C3S3.py: code to compute small extensions of number fields

#######################################################################
#
# Copyright 2018 John Cremona
#
# This is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by the
# Free Software Foundation; either version 2 of the License, or (at your
# option) any later version.
#
# This code is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
# for more details.
#
# You should have received a copy of the GNU General Public License
# along with this file; if not, write to the Free Software Foundation,
# Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301, USA
#
#######################################################################

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
# Angelos Koutsianas's thesis for some details.  Where we use Kummer
# theory to construct cyclic extensions we could alternatively use
# Class Field Theory, and we expect to write code for that once
# https://trac.sagemath.org/ticket/15829 is finished.
#
#

from sage.all import ProjectiveSpace, polygen, proof, ZZ, QQ, PolynomialRing, Set, GF, prod
from poly_utils import pol_simplify

# The following line means that class groups, etc, are computed
# non-rigorously (assuming GRH) which makes everything run faster.

proof.number_field(False)

############## basic utility functions #################################

def uniquify(S):
    r"""
    Return a list of the unique elements of S.
    """
    return list(Set(S))

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
    #print("Checking whether {} in {} is an S-unit with S={}...".format(a,K,S))
    try:
        ok = a.is_S_unit(S)
    except AttributeError:
        ok = K.ideal(a).is_S_unit(S)
    #print("... {}".format(ok))
    return ok

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
    # return L.relative_discriminant().is_S_unit(S)
    if debug:
        print("testing ramification of {}".format(L))
    f = L.defining_polynomial()
    d = f.discriminant()
    K = f.base_ring()

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

    if p is not None:
        p = K(p)
        bads = [P for P in bads if p.valuation(P)>0]
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
    for P in bads:
        if debug:
            print("Testing whether {} is ramified in L".format(P))
        for Q in L.primes_above(P):
            e = Q.relative_ramification_index()
            if e>1:
                if debug:
                    print("NO")
                return False
    if debug:
        print("OK")
    return True

def selmer_group_projective(K,S,p):
    r"""Return iterator over K(S,p) up to scaling.

    INPUT:

    - ``K`` (number field) -- a number field, or ``QQ``.

    - ``S`` (list) -- a list of prime ideals in ``K``, or primes.

    - ``p`` (prime) -- a prime number.

    - ``debug`` (boolean, default ``False``) -- debug flag.

    OUTPUT:

    (iterator) Yields all non-zero elements of `\mathbb{P}(K(S,p))`,
    where `K(S,p)` is viewed as a vector space over `GF(p)`.  In other
    words, yield all non-zero elements of `K(S,p)` up to scaling.

    ..note::

      This could easily be moved into K.selmer_group_iterator(S,p) as
      an option.

  """
    KSgens = K.selmer_generators(S=list(set(S)), m=p)
    for ev in ProjectiveSpace(GF(p),len(KSgens)-1):
        yield prod([q ** e for q, e in zip(KSgens, list(ev))], K.one())

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
    S = uniquify(S)
    x = polygen(K)
    # if some primes above 2 are not in S then a further check is required
    if is_S_unit(K(2),S):
        test = lambda a: True
    else:
        test = lambda a: unramified_outside_S(K.extension(x**2-a,'t2'), S, 2)
    return [pol_simplify(x**2-a) for a in K.selmer_group_iterator(S,2) if not a.is_square() and test(a)]

############## C3 (cyclic cubic extensions) ###############################

def C3_extensions(K,S, verbose=False, debug=False):
    r"""Return all `C_3` extensions of ``K`` unramified outside ``S``.

    INPUT:

    - ``K`` (number field) -- a number field, or ``QQ``.

    - ``S`` (list) -- a list of prime ideals in ``K``, or primes.

    - ``verbose`` (boolean, default ``False``) -- verbosity flag.

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
    S = uniquify(S)
    x = polygen(K)
    if verbose:
        print("finding C3 extensions over {} unramified outside {}".format(K,S))

    if K(-3).is_square(): ## K contains cube roots of unity
        if is_S_unit(K(3),S): # primes dividing 3 are in S -- easy case
            test = lambda a: True
        else:
            test = lambda a: unramified_outside_S(K.extension(x**3-a,'t3'), S, 3)
        # use K(S,3), omitting trivial element and only including one of a, a^-1:
        return [pol_simplify(x**3-a) for a in selmer_group_projective(K,S,3) if test(a)]

    # now K does not contain the cube roots of unity.  We adjoin them.
    # See Angelos Koutsianas's thesis Algorithm 3 (page 45)

    if verbose:
        print("finding alphas")

    # Find downstairs Selmer group and maps:
    KS3, KS3_gens, from_KS3, to_KS3 = K.selmer_space(S,ZZ(3))
    if verbose:
        print("Downstairs 3-Selmer group has dimension {}".format(KS3.dimension()))

    # Find upstairs Selmer group and maps:
    K3 = K.extension(x**2+x+1,'z3')
    nm = lambda p: p if p in ZZ else p.absolute_norm()
    S3 = sum([K3.primes_above(P) for P in S if nm(P)%3!=2],[])
    K3S3, K3S3_gens, from_K3S3, to_K3S3 = K3.selmer_space(S3,ZZ(3))
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
    if check_3 and verbose:
        print("3 is not an S-unit, so we will need to check ramification at primes above 3 not in S")
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
    if verbose:
        print("{} polys found".format(len(polys)))
    if K.absolute_degree()<6:
        if verbose:
            print("-- applying pol_simplify...")
        polys = [pol_simplify(f) for f in polys]
    return polys

############## S3 (non-cyclic cubic extensions) ###############################

def S3_extensions(K,S, D=None, check_D=True, verbose=False):
    r"""Return irreducible cubics whose splitting fields are `S_3`
    extensions of ``K`` unramified outside ``S``.

    If ``D`` is not None then it must be an element of $K^*$ such that
    $K(\sqrt(D))$ is a quadratic extension unramified outside ``S``,
    and only cubics with discriminant ``D`` (mod squares) are
    returned.  This condition on ``D`` is checked unless check_D is
    False.

    INPUT:

    - ``K`` (number field) -- a number field, or ``QQ``.

    - ``S`` (list) -- a list of prime ideals in ``K``, or primes.

    - ``D`` (number field element) -- a nonzero element of ``K`` such
      that $K(\sqrt{D})$ is quadratic is unramified outside ``S``.

    - ``verbose`` (boolean, default ``False``) -- verbosity flag.

    OUTPUT:

    (list) A list of monic polynomials of degree 3 in `K[x]` defining
    all non-Galois cubic extensions of `K` unramified outside `S` (or
    just those whose disciminant is ``D`` if ``D`` is given).

    """
    S = uniquify(S)
    Kx = PolynomialRing(K, 'x')
    if verbose:
        if D:
            print("finding S3 extensions over {} unramified outside {} with discriminant {}".format(K,S,D))
        else:
            print("finding S3 extensions over {} unramified outside {}".format(K,S))


    if not D:
        Ds = [f.discriminant() for f in C2_extensions(K,S)]
        if K is QQ:
            Ds = [d.squarefree_part() for d in Ds]
        if verbose:
            print("{} possible quadratic subfields".format(len(Ds)))
        cubics = []
        for d in Ds:
            #print("working on d={}".format(d))
            cubics1 = S3_extensions(K,S, d, False, verbose)
            if verbose:
                print("d={}: {} cubics found: {}".format(d,len(cubics1),cubics1))
            cubics = cubics+cubics1
        return cubics

    D = K(D)
    M = K.extension(Kx([-D,0,1]), 't1')
    if check_D:
        if not unramified_outside_S(M, S):
            raise ValueError("invalid discriminant D={} (quadratic not unramified outside {})".format(D, S))

    # compute the generator of Gal(M/K)
    g = next(e for e in M.automorphisms() if e(M.gen()) != M.gen())

    # find the primes of M above those in S
    SM = sum([M.primes_above(p) for p in S],[])

    # if we add in primes above 3 here then the C3 extension search
    # need not bother about checking ramification above 3, so will be
    # faster.  We'll do that check later where it will be quick as not so
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

    if len(cubics)==0:
        return []

    # Now from these cubics L/M/K we must pick out those which are
    # Galois and have group S3 (not C6):

    Mx = cubics[0].parent()

    # test function for cubics in M[x].  If they define S3 Galois
    # extensions of K then we return a cubic over K with the same
    # splitting field, otherwise we return False.

    # The following function is base on Section 4.3 of AK's thesis.
    # There it was assumed that the next-to-leading coefficient of f
    # is 0, which would be the case if f had the form x^3-c, but since
    # the cubics returned by C3_extensions have been simplified, we
    # cannot assume this.  Instead, we can ensure that the polynomial
    # h constructed is irreducible simply by testing that y=a1+b1 is
    # not in K (instead of testing that it is not 0 as in AK), and it
    # cannot be that both a1+b1 and a1+b2 are in K (if so then d=b2-b1
    # is in K but the automorphism sigma takes b1 to b2 so cannot then
    # have order p, following AK's notation).

    def test(f):
        if verbose:
            print("testing {}".format(f))
        fbar = Mx([g(c) for c in f.coefficients(sparse=False)])
        if verbose:
            print("f = {}, fbar = {}".format(f,fbar))
        if f==fbar:
            if verbose:
                print("easy case as this f is in K[x]")
            h = Kx([c[0] for c in f.coefficients(sparse=False)])
            if h.discriminant().is_square():
                return False
            if verbose:
                print("*** returning {} as valid".format(h))
            return h

        # f splits over L, since L/M is C3.  Test if fbar also splits
        # over L, as otherwise L/K is not Galois:
        L = f.base_ring().extension(f,'c')
        fbar_roots = fbar.roots(L, multiplicities=False)
        if len(fbar_roots)==0:
            if verbose:
                print("*** not Galois over K")
            return False

        # now L/K is Galois.  We test that it is S3 not C6, and find a
        # cubic over K with splitting field L/K:
        f_roots = f.roots(L, multiplicities=False)
        if verbose:
            print("roots of f:    {}".format(f_roots))
            print("roots of fbar: {}".format(fbar_roots))

        y = f_roots[0]+fbar_roots[0]
        h = y.minpoly()
        if h.degree()==1:
            y = f_roots[0]+fbar_roots[1]
            h = y.minpoly()
            assert h.degree()==3
        # these two cannot both be in K (see comment above), and when
        # not in K it has degree 3 over K so its min poly is the cubic
        # we seek.
        if verbose:
            print("f, fbar distinct.  Using y={} with minpoly {}".format(y,h))
        # h is in K[x] when S3. If h is not in K[x] then certainly C6;
        # if h is in K[x] it may be C6 and we have to check the
        # discriminant later.  So far h is in M[x] since y is in L and
        # L is a relative extension of M.  We test that all the coeffs
        # of h are in fact in K, and if so convert h to a polynomial
        # in K[x]:
        coeffs = h.coefficients(sparse=False)
        if any(c[1]!=0 for c in coeffs):
            if verbose:
                print("*** C6, not S3 over K")
            return False
        h = Kx([c[0] for c in coeffs])
        if verbose:
            print("h = {}".format(h))
        if h.discriminant().is_square():
            if verbose:
                print("*** C6, not S3 over K (discriminant is square)")
            return False
        assert h.is_irreducible()
        if verbose:
            print("*** returning {} as valid".format(h))
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
        print("{} polys (before final test): {}".format(len(polys),polys))

    # The only remaining check is that the extensions L/K might be ramified at primes above 3 if these are not all in S.
    check_3 = not is_S_unit(K(3),S)
    if check_3:
        polys = [h for h in polys if unramified_outside_S(K.extension(h,'t2'),S,3)]

    if verbose:
        print("polys  (after final test, before simplification): {}".format(polys))

    if K.absolute_degree()<6:
        if verbose:
            print("-- applying pol_simplify...")
        polys = [pol_simplify(f) for f in polys]
        if verbose:
            print("polys  (after simplification): {}".format(polys))
    else:
        if verbose:
            print("skipping simplification step as base field has absolute degree>6")
    return polys

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
    return C3_extensions(K,S, verbose=verbose) + S3_extensions(K,S, verbose=verbose)

