# KSp.py: code to compute p-Selmer groups of number fields

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
# This file contains SageMath code to compute K(S,p) where
#
# K is a number field
# S is a finite set of primes of K
# p is a prime number
#
# Author: John Cremona (based on code he wrote for Magma originally)
#
# Note: Sage (as of version 8.2) has methods K.selmer_group(S,m) which
# returns a list of generators of K(S,m) with m>0 not necessarily
# prime, together with (optionally) their orders; and also
# K.selmer_group_iterator(S,m) which returns an iterator through all
# elements of K(S,m).  But these functions do not implement any
# inverse map taking an element of K^* representing an element of
# K^*/(K^*)^m lying in K(S,m) and returning a vector of its exponenets
# with respect to the generators.  We need this and have implemented
# it here.  The code here will be submitted to SageMath through
# https://trac.sagemath.org/ticket/16496.
#

# The main function here is pSelmerGroup().  All the preceding ones
# are subsidiary utilities.  Some of these are only to allow the same
# code to work over QQ as over any number field.

from sage.all import Matrix, GF, prod, VectorSpace, ProjectiveSpace, QQ, ZZ

def IdealGenerator(I):
    r"""Return the generator of a principal ideal.

    INPUT:

    - ``I`` (fractional ideal or integer) -- either a fractional ideal of a
      number field, which must be principal, or a rational integer.

    OUTPUT:

    A generator of I when I is a principal ideal, else I itself.
    """
    try:
        return I.gens_reduced()[0]
    except AttributeError:
        return I

# fractional ideals have no support method, but field elements do

def Support(a):
    r"""Return the support (list of prime factors) of a.

    INPUT:

    - ``a`` (fractional ideal, number field element, or integer) --
      either a fractional ideal of a number field, or a nonzero
      element of a number field, or a rational integer.

    OUTPUT:

    The list of prime factors of ``a``.  In case ``a`` is a rational
    integer this is a list pf prime numbers, otherwise a list of prime
    ideals.

    """
    try:
        return a.support()
    except AttributeError:
        return a.prime_factors()

def coords_in_C_p(I,C,p):
    r"""Return coordinates of the ideal ``I`` with respect to a basis of
    the ``p``-torsion of the ideal class group ``C``.

    INPUT:

    - ``I`` (ideal) -- a fractional ideal of a number field ``K``,
      whose ``p``'th power is principal.

    - ``C`` (class group) -- the ideal class group of ``K``.

    - ``p`` (prime) -- a prime number.

    OUTPUT:

    The coordinates of the ideal class `[I]` in the `p`-torsion subgroup `C[p]`.
    """
    c = C(I).exponents()
    non_p_indices = [i for i,n in enumerate(C.gens_orders()) if not p.divides(n)]
    assert all([c[i]==0 for i in non_p_indices])
    p_indices = [(i,n//p) for i,n in enumerate(C.gens_orders()) if p.divides(n)]
    assert all([c[i]%n==0 for i,n in p_indices])
    return [(c[i]//n)%p for i,n in p_indices]

def coords_in_C_mod_p(I,C,p):
    r"""Return coordinates of the ideal ``I`` with respect to a basis of
    the ``p``-cotorsion of the ideal class group ``C``.

    INPUT:

    - ``I`` (ideal) -- a fractional ideal of a number field ``K``.

    - ``C`` (class group) -- the ideal class group of ``K``.

    - ``p`` (prime) -- a prime number.

    OUTPUT:

    The coordinates of the ideal class `[I]` in the `p`-cotorsion group `C/C^p`.
    """
    c = C(I).exponents()
    p_indices = [i for i,n in enumerate(C.gens_orders()) if p.divides(n)]
    return [c[i]%p for i in p_indices]

def root_ideal(I,C,p):
    r"""Return the ``p``'th root of an ideal with respect to the class group.

    INPUT:

    - ``I`` (ideal) -- a fractional ideal of a number field ``K``,
      whose ideal class is a ``p``'th power.

    - ``C`` (class group) -- the ideal class group of ``K``.

    - ``p`` (prime) -- a prime number.

    OUTPUT:

    An ideal `J` such that `J^p` is in the ideal class `[I]`.
    """
    v = C(I).exponents()
    # In the line below, e=(vi/p)%n should satisfy p*e=vi (mod n)
    w = [vi//p if p.divides(n) else (vi/p)%n for vi,n in zip(v,C.gens_orders())]
    return prod([J**wi for wi,J in zip(w,C.gens_ideals())], C.number_field().ideal(1))

def coords_in_U_mod_p(u,U,p):
    r"""Return coordinates of a unit ``u`` with respect to a basis of the
    ``p``-cotorsion of the unit group ``U``.

    INPUT:

    - ``u`` (algebraic unit) -- a unit in a number field ``K``.

    - ``U`` (unit group) -- the unit group of ``K``.

    - ``p`` (prime) -- a prime number.

    OUTPUT:

    The coordinates of the ideal class `u` in the `p`-cotorsion group `U/U^p`.
    """
    co = U.log(u)
    if not p.divides(U.zeta_order()):
        co = co[1:]
    return  [c%p for c in co]

def basis_for_p_cokernel(S,C,p):
    r"""Return a basis for the group of ideals supported on S (mod
    p-powers) whose class in the class group C is a p'th power,
    together with a function which takes the S-exponents of such an
    ideal and returns its coordinates on this basis.

    INPUT:

    - ``S`` (list) -- a list of prime ideals in a number field ``K``.

    - ``C`` (class group) -- the ideal class group of ``K``.

    - ``p`` (prime) -- a prime number.

    OUTPUT:

    (tuple) (``b``, ``f``) where

    - ``b`` is a list of ideals which is a basis for the group of
    ideals supported on ``S`` (modulo ``p``'th powers) whose ideal
    class is a ``p``'th power, and

    - ``f`` is a function which takes such an ideal and returns its
    coordinates with respect to this basis.
    """
    M = Matrix(GF(p),[coords_in_C_mod_p(P,C,p) for P in S])
    k = M.left_kernel()
    bas = [prod([P**bj.lift() for P,bj in zip(S,b.list())],
                C.number_field().ideal(1)) for b in k.basis()]
    f = lambda v: k.coordinate_vector(v)
    return bas,f

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
    KSgens = K.selmer_group(S=S, m=p)
    for ev in ProjectiveSpace(GF(p),len(KSgens)-1):
        yield prod([q ** e for q, e in zip(KSgens, list(ev))], K.one())

# The function itself

def pSelmerGroup(K, S, p, debug=False):
    r"""Return the ``p,S``-Selmer group of the number field containing the
    ideals in ``S``

    INPUT:

    - ``K`` (number field) -- a number field, or ``QQ``.

    - ``S`` (list) -- a list of prime ideals in ``K``.

    - ``p`` (prime) -- a prime number.

    - ``debug`` (boolean, default ``False``) -- debug flag.

    OUTPUT:

    (tuple) ``KSp``, ``KSp_gens``, ``from_KSp``, ``to_KSp`` where

    - ``KSp`` is an abstract vector space over `GF(p)` isomorphic to `K(S,p)`;

    - ``KSp_gens`` is a list of elements of `K^*` generating `K(S,p)`;

    - ``from_KSp`` is a function from ``KSp`` to `K^*` implementing
      the isomorphism from `K(S,p)` to `K(S,p)` as a subgroup of
      `K^*/(K^*)^p`;

    - ``to_KSP`` is a partial function from `K^*` to ``KSp`` defined
      on elements `a` whose image in `K^*/(K^*)^p` lies in `K(S,p)`,
      mapping them via the inverse isomorphism to the abstract vector
      space ``KSp``.

    """
    # Input check: p and all P in S must be prime.

    if not all(P.is_prime() for P in S):
        raise ValueError("elements of S must all be prime")
    if not p.is_prime():
        raise ValueError("p must be prime")

    F = GF(p)

    # Step 1. The unit contribution: all fundamental units, and also the
    # generating root of unity if its order is a multiple of p; we just
    # take generators of U/U^p.  These have valuation 0 everywhere.

    hK = K.class_number()
    C = K.class_group()
    hKp = (hK%p == 0)

    if K == QQ:
        if p == 2:
            ulist = [QQ(-1)]
        else:
            ulist = []
    else:
        U = K.unit_group()
        ulist = U.gens_values()
        if U.zeta_order()%p:
            ulist = ulist[1:]
    if debug: print("{} generators in ulist = {}".format(len(ulist),ulist))

    # Step 2. The class group contribution: generators of the p'th
    # powers of ideals generating the p-torsion in the class group.
    # These have valuation divisible by p everywhere.

    if hKp:
        betalist = [IdealGenerator(c**n) for c,n in zip(C.gens_ideals(), C.gens_orders()) if n%p==0]
    else:
        betalist = []
    if debug: print("{} generators in betalist = {}".format(len(betalist),betalist))

    # Step 3. The part depending on S: one generator for each ideal A
    # in a basis of those ideals supported on S (modulo p'th powers of
    # ideals) which is a p'th power in the class group.  We find B
    # such that A/B^p is principal and take a generator of that, for
    # each A in a generating set.

    if hK > 1:
        T, f = basis_for_p_cokernel(S,C,p)
        alphalist = [IdealGenerator(I/root_ideal(I,C,p)**p) for I in T]
    else:
        f = lambda x:x
        alphalist = [IdealGenerator(P) for P in S]

    if debug: print("{} generators in alphalist = {}".format(len(alphalist), alphalist))

    # Now we have the generators of K(S,p), and define K(S,p) as an
    # abstract vector space:

    KSp_gens = alphalist + betalist + ulist
    if debug: print("Generators of K(S,p) = {} (dimension {})".format(KSp_gens, len(KSp_gens)))
    KSp = VectorSpace(GF(p), len(KSp_gens))

    # Now we define maps in each direction from the abstract space and K^*.

    # Define the easy map from KSp into K^*:

    def from_KSp(v):
        return prod([g**vi for g,vi in zip(KSp_gens,v)], K(1))

    # Define the hard map from (a subgroup of) K^* to KSp:

    def to_KSp(a):
        # Check that a is in K(S,p):
        assert a != 0
        assert all(P in S or a.valuation(P)%p==0 for P in a.support())

        # 1. (a) is a p'th power mod ideals in S, say (a)=AB^p, where
        # A is supported on S and is a linear combination of the
        # ideals T above.  Find the exponents of the P_i in S in A:

        S_vals = [F(a.valuation(P)) for P in S]
        avec = list(f(S_vals)) # coordinates of A w.r.t ideals in T (mod p'th powers)
        a1 = prod((alpha**e for alpha,e in zip(alphalist,avec)), K(1))
        a /= a1
        if debug: print("alpha component is {} with coords {}".format(a1,avec))
        if debug:
            if K==QQ:
                print("continuing with quotient {} whose ideal should be a {}'th power: {}".format(a,p,a.factor()))
            else:
                print("continuing with quotient {} whose ideal should be a {}'th power: {}".format(a,p,K.ideal(a).factor()))

        # 2. Now (a) is a p'th power, say (a)=B^p.
        # Find B and the exponents of [B] w.r.t. basis of C[p]:

        supp = a.support()
        vals = [a.valuation(P) for P in supp]
        assert all(v%p==0 for v in vals)
        if K==QQ:
            B = prod((P**(v//p) for P,v in zip(supp,vals)),K(1))
            assert B**p == a.abs()
        else:
            B = prod((P**(v//p) for P,v in zip(supp,vals)),K.ideal(1))
            assert B**p == K.ideal(a)
        if debug:
            print("B={}".format(B))
            print("a={}".format(a))

        if hKp:
            bvec = coords_in_C_p(B,C,p)
            a2 = prod((beta**e for beta,e in zip(betalist,bvec)), K(1))
            a /= a2
            supp = a.support()
            vals = [a.valuation(P) for P in supp]
            assert all(v%p==0 for v in vals)
            B = prod((P**(v//p) for P,v in zip(supp,vals)),K.ideal(1))
            assert B**p == K.ideal(a)
        else:
            bvec = []
            a2 = 1

        if debug: print("beta component is {} with coords {}".format(a2,bvec))
        if debug: print("continuing with quotient {} which should be a p'th power times a unit".format(a))

        # 3. Now (a) = (c)^p for some c, so a/c^p is a unit

        if K!=QQ:
            assert B.is_principal()
        if debug: print("B={}".format(B))
        a3 = B if K==QQ else IdealGenerator(B)
        if debug: print("a3={}".format(a3))
        a /= a3**p
        if debug: print("dividing by {}th power of {}".format(p,a3))
        if debug: print("continuing with quotient {} which should be a unit".format(a))

        #4. Now a is a unit

        # NB not a.is_unit which is true for all a in K^*.  One could
        # also test K.ring_of_integers()(a).is_unit().
        if K==QQ:
            assert a.abs()==1
        else:
            assert K.ideal(a).is_one()

        if K == QQ:
            if p == 2:
                cvec = [1] if a == -1 else [0]
            else:
                cvec = []
        else:
            cvec = coords_in_U_mod_p(a,U,p)
        if debug: print("gamma component has coords {}".format(cvec))

        return KSp(avec + bvec + cvec);

    return KSp, KSp_gens, from_KSp, to_KSp


"""Notes on computing the map to_KSp:

Given a in K(S,p):

(1) Write the principal ideal (a) in the form AB^p with A supported by
S and p'th power free.

Set IS = group of ideals spanned by S mod p'th powers, and
ISP=subgroup of that which map to 0 in C/C^p.

(2) Convert A to an element of ISP, hence find the coordinates of a
with respect to the generators in alphalist.

(3) Dividing out by that, now (a)=B^p (with a different B).

Write the ideal class [B], shose p'th power is trivial, in terms of
the generators of C[p]; then B=B1*(b) where the coefficients of B1
with respect to generators of Cl[p] give the coordinates of the result
with respect to the generators in betalist.

(4) Dividing out by that, and by b^p, we have (a)=(1), so a is a unit.

Now a can be expressed in terms of the unit generators (fundamental
units and, if necessary, a root of unity.

"""

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

