r"""For K a number field, S a finite set of primes of K and G in
{C4,D4,V4,A4,S4} we find all extensions of K with Galois group G and
unramified outside S.  In the case of C4, A4, S4 it is possible to
specify the cubic resolvent.  It is also possible to specify the
discriminant field.  In all cases the output is a list of quartics,
always irreducible except in the case of V4.
"""

from sage.all import polygen, QQ, ZZ, PolynomialRing
from poly_utils import pol_simplify
from C2C3S3 import C2_extensions, C3_extensions, S3_extensions, uniquify, is_S_unit, unramified_outside_S

############## V4 (biquadratic extensions) ###############################

r""" A V4 extension M/K has the form K(sqrt(d1),sqrt(d2),sqrt(d3)) with
d3=d1*d2 mod squares and d1,d2 independent mod squares.

We provide two options:
 (1) specify a given quadratic subfield K(sqrt(d1)) (default None);
 (2) specify a given discriminant d (Default d=1).

If both are given and d!=d1 then the field is unique.

An irreducible quartic with splitting field M such as the minimal
  polynomial X^4-2(d1+d2)X^2+(d1-d2)^2 of sqrt(d1)+sqrt(d2) has square
  discriminant.

To have discriminant field K(sqrt(d3)), for example, we need a
reducible quartic (X^2-d1)(X^2-d2).
"""

def disc_index(ds, D):
    """
    Return the index of D in the list ds, mod squares.
    """
    for i,d in enumerate(ds):
        if D==d: # special case
            return i
        if (D*d).is_square():
            return i
    return -1
    
def discs_mod_D(ds, D):
    """Given a list of discriminants which are the nontrivial elements of
    some finite subgroup G of K^*/(K^*)^2, and an element D of G,
    return a list of nontrivial coset representatives of G/<D>.
    """
    if D.is_square():
        return ds
    
    K = D.parent()
    if K==QQ:
        ds = [d.squarefree_part() for d in ds]
    iD = disc_index(ds,D)
    if iD == -1:
        raise RuntimeError("discriminant {} is not in the list {} mod squares".format(D,ds))

    # The map d -> d*D mod squares is a product of transpositions on
    # ds (mod squares) with no fixed points.  We return those d for
    # which d*D is later in the list.

    # This one-liner works but does not catch problems:

    #return [d for i,d in enumerate(ds) if disc_index(ds,d*D)<i]

    perm = [disc_index(ds,d*D) for d in ds]
    if any([i != iD and j == -1 for i,j in enumerate(perm)]):
        raise RuntimeError("discriminant list {} not closed under multiplication by {} mod squares".format(ds,D))
    return [d for i,d in enumerate(ds) if i != iD and perm[i] < i]

def V4_extensions(K,S, D=None, check_D=True, verbose=False):
    r"""Return quartics whose splitting field M is a V4 extension of K
    unramified outside S.

    If D is not None then K(sqrt(D)) must be unramified outside S and the
    quartics returned will have discriminant D, so they will be
    reducible and their splitting fields M will contain K(sqrt(D)).

    If D is None then irreducible quartics with square discriminant
    defining all V4 extensions of K unramified outside S will be
    returned.

    If you want an irreducible quartic defining a V4 with K(sqrt(d))
    as a subfield, call this with D=d, and for each quartic
    X^4+a*X^2+b returned use X^4-2*a*X^2+(a^2-4*b) instead.
    
    [X^4+a*X^2+b = (X^2-d1)*(X^2-d2) with a = -(d1+d2), b = d1*d2.
    The minimum polynomial of sqrt(d1)+sqrt(d2) is
    X^4-2*(d1+d2*X^2+(d1-d2)^2 = X^4+2*a*X^2+(a^2-4*b).]

    """
    S = uniquify(S)
    Kx = PolynomialRing(K, 'x')

    if D:
        D = K(D)
        if D.is_square():
            D = None
        else:
            if check_D:
                M = K.extension(Kx([-D,0,1]), 'm')
                if not unramified_outside_S(M, S):
                    raise ValueError("invalid discriminant D={} (quadratic not unramified outside {})".format(D, S))

    C2s = C2_extensions(K,S)
    ds = [f.discriminant() for f in C2s]
    if K==QQ:
        ds = [d1.squarefree_part() for d1 in ds]

    if not D:
        # We want to enumerate the 2-dimensional subspaces, using just
        # one unordered pair {a,b} from each unordered triple {a,b,c}
        # with c=a*b mod squares.  To do this we only use ordered
        # pairs [a,b] such that i(a) < i(b) < i(c), where i() gives
        # the index in the list.
        
        ab_pairs = []
        for i,a in enumerate(ds):                 # a runs through all
            for j,b in enumerate(ds[i+1:], i+1):  # b is after a in the list
                c = a*b
                if K==QQ:
                    c = c.squarefree_part()
                k = disc_index(ds, c)
                if k>j:                           # use c only if it is after b
                    #print((i,j,k))
                    ab_pairs.append([a,b])
        #print("ab pairs = {}".format(ab_pairs))
        return [pol_simplify(Kx([(a-b)**2, 0, -2*(a+b), 0, 1])) for a,b in ab_pairs]
                   # irreducible, disc=1 mod squares
    else:
        # Remove D and one of each pair d, d*D from the list:
        d1s = discs_mod_D(ds, D) # will check that D is in ds mod squares
        d2s = [d1*D for d1 in d1s]
        if K==QQ:
            d2s = [d2.squarefree_part() for d2 in d2s]
        return [Kx([d1*d2, 0, -(d1+d2), 0, 1]) for d1,d2 in zip(d1s,d2s)]
                  # (x^2-d1)(x^2-d2), disc=d mod squares
                    

############## C2+ (quartics which factor as a product of 2 irreducible quadratics) ###############################

# This is needed for working with projective mod-3 Galois
# representations, since the representation may be irreducible with
# image C2 generated by an element of PGL(2,3) which has no fixed
# points in P^1(GF(3)) and minimal polynomial x^2+1.  The kernel field
# is defined by a suitable quadratic f(x), and here we construct the
# associated quartic f(x)*f(x+1), which has square discriminant and is
# such that the Galois group acts by permutation of the roots as the
# subgroup C2+ of S4, generated by a product of two transpositions.

def C2_plus_extensions(K,S, D=None, check_D=True, verbose=False):
    r"""Return quartics whose splitting field is a quadratic extension of
    K, unramified outside S, which factor into two irreducible
    quadratics with the same discriminant and with distinct roots.

    If D is not None then it should be a nonzero element of K such
    that K(sqrt(D)) is quadratic and unramified outside S.  This
    condition is checked unless check_D is False. In this case only
    one quartic is returned, whose splitting field contains
    K(sqrt(D)).

    """
    if verbose:
        if D:
            print("finding C2+ quartics over {} with discriminant {}, unramified outside {}".format(K,D,S))
        else:
            print("finding C2+ quartics over {}, unramified outside {}".format(K,S))
    S = uniquify(S)
    Kx = PolynomialRing(K, 'x')
    x = Kx.gen()

    if not D:
        return [pol_simplify(f*f(x+1)) for f in C2_extensions(K,S)]
        
    D = K(D)
    f = Kx([-D,0,1])
    if check_D:
        M = K.extension(f, 'm')
        if not unramified_outside_S(M, S):
            raise ValueError("invalid discriminant D={} (quadratic not unramified outside {})".format(D, S))
    return [pol_simplify(f*f(x+1))]


############## C4 (cyclic quartic extensions) ###############################

r""" C4 extensions have unique quadratic subextensions M and are
constructed as suitable quadratic extensions of these.  If
M=K(sqrt(D)) then the condition on a in M^* for M(sqrt(a)) to be
cyclic over K is that N_{M/K}(a) be D times a square.  (If the norm is
a square you get a biquadratic over K, while in other cases M(sqrt(a))
is non-Galois over K and its Galois closure M(sqrt(a),sqrt(a')) is D4
over K (where a' is the M/K-conjugate of a).

If a has min poly X^2-tX+n with n=D (mod squares) then the quartic is
X^4-tX^2+n with discriminant n mod squares.

"""

def C4_extensions(K,S, D=None, check_D=True, verbose=False):
    r"""Return irreducible C4 extensions of K unramified outside S.

    If D is not None then it should be a nonzero element of K such
    that K(sqrt(D)) is quadratic and unramified outside S.  This
    condition is checked unless check_D is False. In this case only
    quartics with discriminant D (mod squares) are returned, whose
    splitting field contains K(sqrt(D)).

    """
    S = uniquify(S)
    Kx = PolynomialRing(K, 'x')

    if verbose:
        if D:
            print("finding C4 quartics over {} with discriminant {}, unramified outside {}".format(K,D,S))
        else:
            print("finding C4 quartics over {}, unramified outside {}".format(K,S))

    if not D:
        Ds = [f.discriminant() for f in C2_extensions(K,S)]
        if K is QQ:
            D = [d.squarefree_part() for d in Ds]
            
        return sum([C4_extensions(K,S, D=d, check_D=False, verbose=verbose) for d in Ds], [])
        
    D = K(D)
    M = K.extension(Kx([-D,0,1]), 'm')
    if check_D:
        if not unramified_outside_S(M, S):
            raise ValueError("invalid discriminant D={} (quadratic not unramified outside {})".format(D, S))

    SM = sum([M.primes_above(P) for P in S],[])
    xM = polygen(M)

    # Find the alphas defining cyclic extensions over K:
    alphas = [a for a in M.selmer_group_iterator(SM,2) if (D*a.relative_norm()).is_square()]

    # if some primes above 2 are not in S then a further check is required
    if not is_S_unit(M(2), SM):
        alphas = [a for a in alphas if unramified_outside_S(M.extension(xM**2-a,'t4'),SM)]

    if K==QQ:
        norms  = [a.norm() for a in alphas]
        traces = [a.trace() for a in alphas]
    else:
        norms  = [a.norm(K) for a in alphas]
        traces = [a.trace(K) for a in alphas]

    return [pol_simplify(Kx([n, 0, -t, 0, 1])) for n,t in zip(norms, traces)]

############## D4 (dihedral quartic extensions) ###############################

r""" A D4 extension M/K has a unique biquadratic subfield
L=K(sqrt(d1),sqrt(d2)) such that M is cyclic over K(sqrt(d1*d2)) but
is V4 over K1=K(sqrt(d1)) and over K2=K(sqrt(d2)).  There are four
other quartic subfields in two conjugate pairs: L1=K1(sqrt(a1)) with
conjugate L1'=K1(sqrt(a1')), which contains K1 but has discriminant d2
(mod squares), and L2=K2(sqrt(a2)) with conjugate L2'=K2(sqrt(a2'))
which contains K2 but has discriminant d1 (mod squares).  The fields
L1, L2 are called sibling fields.

So we have two possible ways to express M as the splitting field of an
irreducible quartic q: either q=q1, a defining polynomial for L1 with
discriminant d1, or q=q2, a defining polynomial for L2 with
discriminant d1.

The D4_extension functions return quartics whose Galois group is D4,
so will return both siblings by default.  If the user wants all
possible splitting fields but one one of each pair of siblings, they
will have to exclude half the quartics output themselves; it would be
possible to have an option to do this automatically but this has not
been implemented.

Optionally one can specify the discriminant d1 (say) and then the
output will only contain quartics with discriminant d1, hence at most
one of each sibling pair.

The strategy is to form L1=K(sqrt(d1)), either from the given d1 or
running through a list f all quadratic discriminants over K unramified
outside S, find all a1 in L1 with norm d1 (mod squares), so a1 has
minimum polynomial X^2-t*X+n with n=d1 (mod squares) and
q1=X^4-t*X^2+n while q2=(X^2-t)^2-n.  Then disc(q1)=n=d1 (mod squares)
while disc(q2)=t^2-n=d1 (mod squares).  We only return q2 (for each
possible a1 and for each d1).  (If we were to include both q1 and q2
in the output when d1 was not specified, the output would contain two
copies of each sibling since both d1 and d2 would be processed.)

In the application to projective mod-3 Galois representations we will
always know the quartic discriminant d1, since for the projective
image to be D4 the determinant character must be nontrivial and will
cut out a quadratic exteson K(sqrt(d1)).

"""
def D4_extensions(K,S, d1=None, check_d1=True, verbose=False):
    r"""Return quartics whose splitting field is a D4 extension of K
    unramified outside S.

    If d1 is given, it must be such that K(sqrt(d1)) is unramified
    outside S, and the output only contains quartic with discriminant
    d1 (mod squares).  If not (the default) the the function
    recursively calls itself with all possible d1's and returns the
    concatenation of the resulting lists.

    When d1 is given we check that K(sqrt(d1)) is unramified outside S
    by default, unless check_d1 is False: in the recursive call we
    will know that the d1's are good.

    """
    S = uniquify(S)
    Kx = PolynomialRing(K, 'x')
    if verbose:
        if d1:
            print("finding D4 quartics over {} with discriminant {}, unramified outside {}".format(K,d1,S))
        else:
            print("finding D4 quartics over {}, unramified outside {}".format(K,S))

    if not d1:
        d1s = [f.discriminant() for f in C2_extensions(K,S)]
        if K is QQ:
            d1s = [d.squarefree_part() for d in d1s]
            
        return sum([D4_extensions(K,S, d1=d, check_d1=False, verbose=verbose) for d in d1s], [])
        
    d1 = K(d1)
    K1 = K.extension(Kx([-d1,0,1]), 't1')
    if check_d1:
        if not unramified_outside_S(K1, S):
            raise ValueError("invalid discriminant d1={} (quadratic not unramified outside {})".format(d1, S))

    SK1 = sum([K1.primes_above(P) for P in S],[])
    sigma = K1.automorphisms()[1]

    K1S2, K1S2_gens, from_K1S2, to_K1S2 = K1.selmer_space(SK1,ZZ(2))
    # K1S2 is an abstract vector space over GF(2), from_K1S2 maps to
    # K1^* and to_K1S2 maps back, so composing a ->
    # from_K1S2(to_K1S2(a)) returns the canonical representative for
    # each square class.
    
    alphas = [from_K1S2(v) for v in K1S2 if v] # exclude alpha=1

    # keep only those whose norm is not a square in K1, i.e. not a
    # square or d1 times a square in K:
    norms  = [a.relative_norm() for a in alphas]
    alphas = [a for a,n in zip(alphas, norms) if not n.is_square() and not (n*d1).is_square()]

    # remove conjugates (mod squares):
    conj_ind = lambda a: alphas.index(from_K1S2(to_K1S2(sigma(a))))
    alphas = [a for i,a in enumerate(alphas) if not conj_ind(a)<i]

    #print("K1 = {}".format(K1))
    #print("alphas: {}".format(alphas))
    norms  = [a.relative_norm() for a in alphas]
    traces = [a.trace() for a in alphas]

    # Each a with norm n and trace t now determines a D4 extension,
    # K1(sqrt(a), sqrt(d2)) with two possible defining quartics:

    # q1 = X^4 - t*X^2 + n            (contains sqrt(d1), has discriminant ~ n)
    # q2 = X^4 - 2*t*X^2 + (t^2-4*n)  (contains sqrt(n),  has discriminant ~ t^2-4n ~ d1)

    # but we only use q2 since we want discriminant d1.

    # Note that K1(sqrt(a)) may be ramified at primes above 2 not in S (if any).
    
    quartics = [pol_simplify(Kx([t**2-4*n, 0, -2*t, 0, 1])) for t,n in zip(traces,norms)]

    # Final check for ramification above 2.  This could also be done
    # by testing the relative extension K1(sqrt(a))/K1.

    if not is_S_unit(K(2), S):
        quartics = [q for q in quartics if unramified_outside_S(K.extension(q,'t4'),S, 2)]
        if verbose:
            print("After final test at 2 we have {} D4 quartics".format(len(quartics)))

    return quartics

    
############## A4 and S4 quartic extensions ###############################

""" Both A4 and S4 extensions are constructed as V4 extensions of
their resolvent cubic field M, the result being an S4 if M is S3 and
an A4 if M is C3.  We can specify M, or just its discriminant D in
which case all M's with this discriminant are first found, which are
S3's unless D=1 (mod squares) i which case they are C3's.  If neither
then we first find all possible D's.  If both then we check that
disc(M)=D (mod squares).

"""

def A4S4_extensions(K,S, M=None, D=None, check_M=True, check_D=True, verbose=False):
    r"""Return A4 and/or S4 extensions of K unramified outside S.

    If M is not None (the default) it should be a cubic extension of K
    unramified outside S and we only return quartics whose cubic
    resolvent is M, which will be A4 extensions if M is C3, else S4
    extensions.  If check_M is True it will be checked for being
    unramified outside S, and also for having discriminant D if D is
    not None.  M can be either an extension of K or a cubic in K[x].

    If D is not None (the default) it should be a nonzero element of K
    which is either 1 or a non-square such that K(sqrt(D)) is
    unramified outside S, and we only return quartics whose
    discriminant is D (mod squares), which will be A4 extensions if
    D=1, else S4 extensions.

    If both M and D are specified then D is ignored except if check_D
    is True (default) then we check that disc(M)=D (mod squares).

    See also A4_extensions() which preset D=1, and S4_extensions()
    which exclude D=1.

    """
    S = uniquify(S)
    Kx = PolynomialRing(K, 'x')
    x = Kx.gen()
    if verbose:
        mess=f"finding A4/S4 extensions of {K} unramified outside {S}"
        if D:
            mess += f" with discriminant {D}"
        if M:
            mess += f" with cubic resolvent {M.defining_polynomial()}"
        print(mess)
    if not M:
        if D:
            if check_D:
                K2 = K.extension(Kx([-D,0,1]), 't1')
                if not unramified_outside_S(K2, S):
                    raise ValueError("invalid discriminant D={} (quadratic not unramified outside {})".format(D, S))
        else:
            # Find all possible D's (including D=1 later)
            Ds = [f.discriminant() for f in C2_extensions(K,S)]
            if K is QQ:
                Ds = [d.squarefree_part() for d in Ds]
            return sum([A4S4_extensions(K, S, M=None, D=d,    check_D=False, verbose=verbose) for d in Ds],
                       [A4S4_extensions(K, S, M=None, D=K(1), check_D=False, verbose=verbose)])

        if D.is_square():
            Ms = C3_extensions(K, S, verbose=verbose)
        else:
            Ms = S3_extensions(K, S, D=D, check_D=False, verbose=verbose)
        return sum([A4S4_extensions(K, S, M=Mi, D=D, check_M=False, check_D=False, verbose=verbose) for Mi in Ms], [])

    # Now we have a specific cubic resolvent M

    # if M is a cubic polynomial, we replace it with the extension of K it defines:
    try:
        Mpol = Kx(M)
        M = K.extension(Mpol, 'm')
    except TypeError:
        pass
    
    MD = M.relative_discriminant() if M.is_relative() else M.discriminant()
    Mdeg = M.relative_degree() if M.is_relative() else M.degree()
    if check_M:
        if Mdeg != 3:
            raise ValueError("invalid subfield M={} (not cubic)".format(M))
        if not unramified_outside_S(M, S):
            raise ValueError("invalid subfield M={} (cubic but not unramified outside {})".format(M, S))
        if D:
            if not (D*MD).is_square():
                raise ValueError("incompatible subfield M={} and discriminant D={})".format(M, D))
    else:
        if not D:
            D = MD
            
    autos = M.automorphisms()
    name = "S4" if len(autos)==1 else "A4"
    SM = sum([M.primes_above(P) for P in S],[])

    KS2, KS2_gens, from_KS2, to_KS2 = K.selmer_space(S,ZZ(2))
    #print("gens of KS2: {}".format(KS2_gens))

    MS2, MS2_gens, from_MS2, to_MS2 = M.selmer_space(SM,ZZ(2))
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
    # times.  In case M/K is not Galois, there is no repetition.

    if name=="A4":        # remove conjugates (mod squares):
        sigma = autos[1]  # since autos[0] is the identity
        def first_conjugate_index(a):
            sa = sigma(a)
            j = alphas.index(from_MS2(to_MS2(sa)))
            ssa = sigma(sa)
            k = alphas.index(from_MS2(to_MS2(ssa)))
            return min(j,k)
        # Only keep those alphas whose index is minimal among the three conjugates
        alphas = [a for i,a in enumerate(alphas) if not first_conjugate_index(a)>i]

    def make_quartic(a):
        # a is in the cubic extension M/K and has square norm, so has
        # char poly of the form x^3-p*x^2+q*x-r^2.
        r2, q, p, one = list(a.charpoly())
        p = -p
        r2 = -r2
        assert r2.is_square()
        r = r2.sqrt()
        return pol_simplify((x**2-p)**2-8*r*x-4*q)

    quartics = [make_quartic(a) for a in alphas]
    nq1 = len(quartics)
    if verbose:
        print("before testing for repeats we have {} {} quartics".format(nq1, name))
    if K==QQ:
        quartics = [q for i,q in enumerate(quartics)
                    if not any(K.extension(q,'t').is_isomorphic(K.extension(q2,'t2'))
                               for q2 in quartics[:i])]
    else:
        quartics = [q for i,q in enumerate(quartics)
                    if not any(K.extension(q,'t').is_isomorphic_relative(K.extension(q2,'t2'))
                               for q2 in quartics[:i])]
    nq2 = len(quartics)
    if verbose:
        print("after  testing for repeats we have {} {} quartics".format(nq2, name))
    if nq1!=nq2:
        print("repeats detected in {}_extensions_with_resolvent(): {} reduced to {}".format(name, nq1,nq2))
        print("K = {}".format(K))
        print("S = {}".format(S))
        print("M = {}".format(M))
        print("#autos = {}".format(len(autos)))

    # The second V4 layer may be ramified at primes above 2 not in S.
    # So we do a final check (unless S contains all P|2):

    if not is_S_unit(K(2), S):
        quartics = [q for q in quartics if unramified_outside_S(K.extension(q,'t4'),S, 2)]
        if verbose:
            print("After final test at 2 we have {} {} quartics".format(len(quartics), name))
    return quartics

def A4_extensions(K,S, M=None, check_M=True, verbose=False):
    r"""Return irreducible quartic polynomials defining A4 extensions of K
    unramified outside S.

    If M is not None (the default) it should be a cyclic cubic
    extension of K unramified outside S and we only return quartics
    whose cubic resolvent is M.  If check_M is True it will be checked
    for being unramified outside S, and also for having square
    discriminant.

    """
    if verbose:
        if M:
            print("finding A4 extensions of {} over {} unramified outside {}".format(K,M,S))
        else:
            print("finding A4 extensions of {} unramified outside {}".format(K,S))

    return A4S4_extensions(K,S, M=M, check_M=check_M, D=K(1), verbose=verbose)

def S4_extensions(K,S, M=None, check_M=True, D=None, check_D=True, verbose=False):
    r"""Return S4 extensions of K unramified outside S.

    Just call A4S4_extensions() but if M=D=None, omit D=1
    """
    if verbose:
        mess=f"finding S4 extensions of {K} unramified outside {S}"
        if D:
            mess += f" with discriminant {D}"
        if M:
            mess += f" with cubic resolvent {M.defining_polynomial()}"
        print(mess)

    if M or D:
        return A4S4_extensions(K,S, M=M, check_M=check_M, D=D, check_D=check_D, verbose=verbose)
    Ds = [f.discriminant() for f in C2_extensions(K,S)]
    if K is QQ:
        Ds = [d.squarefree_part() for d in Ds]
    return sum([A4S4_extensions(K, S, D=d,    check_D=False, verbose=verbose) for d in Ds], [])


############## "absolutely irreducible" quartic extensions ###############################
#
#  The subgroups whose isomorphs in PGL(2,3) are absolutely irreducible are S4, A4, D4, V4
#

def abs_irred_extensions(K,S, D=None, check_D=True, verbose=False):
    """Return quartics defining extensions of K unramified outside S with
    Galois group S4, A4, D4 or V4.

    If D is not None then only quartics with discriminant D are
    returned.  When D=1 this excludes S4 and D4, and the V4 quartics
    will be irreducible.  When D is non-square then A4 is excluded and
    the V4 quartics will be reducible.

    If D is not None and check_D is True hen we check that either D is
    square or that K(sqrt(D)) is unramified outside S.
    """
    if D and check_D:
        D = K(D)
        if not D.is_square():
            Kx = PolynomialRing(K, 'x')
            if not unramified_outside_S(K.extension(Kx([-D,0,1]), 'm'), S):
                raise ValueError("invalid discriminant D={} (quadratic not unramified outside {})".format(D, S))

    return A4S4_extensions(K,S, D=D, check_D=False) + D4_extensions(K,S, d1=D, check_d1=False) + V4_extensions(K,S, D=D, check_D=False)

############## "irreducible" quartic extensions ###############################
#
#  The subgroups whose isomorphs in PGL(2,3) are irreducible are S4,
#   A4, D4, V4, C4, C2+ (where C2+ is a subgroup of the form
#   <(12)(34)>), these being all subgroups with no fixed points.
#

def irred_extensions(K,S, D=None, check_D=True, verbose=False):
    return abs_irred_extensions(K, S, D, check_D, verbose) + C4_extensions(K,S, D, check_D, verbose) + C2_plus_extensions(K,S, D, check_D, verbose)
