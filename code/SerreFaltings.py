from sage.all import polygen, ZZ, QQ, GF, binomial, Matrix, prod, vector
from KSp import pSelmerGroup
from S4 import A4_extensions_with_resolvent
from T0T1T2 import lam, primes_iter, residue_field

def vec123(K,basis):
    xK = polygen(K)
    quadratics = [xK**2-d for d in basis]
    r = len(basis)
    def vecP(P):
        ones = [lam(pol,P) for pol in quadratics]
        #print("ones: {}".format(ones))
        twos = [ones[i]*ones[j] for i in range(r) for j in range(i+1,r)]
        #print("twos: {}".format(twos))
        threes = [ones[i]*ones[j]*ones[k] for i in range(r) for j in range(i+1,r) for k in range(j+1,r)]
        #print("threes: {}".format(threes))
        vec = ones+twos+threes
        return vec
    return vecP

def NonCubicSet(K,S, verbose=False):
    u = -1 if K==QQ else  K(K.unit_group().torsion_generator())
    from KSp import IdealGenerator
    Sx = [u] + [IdealGenerator(P) for P in S]
    r = len(Sx)
    d123 = r + binomial(r,2) + binomial(r,3)
    vecP = vec123(K,Sx)
    A = Matrix(GF(2),0,d123)
    N = prod(S,1)

    primes = primes_iter(K,None)
    T = []
    while A.rank() < d123:
        p = primes.next()
        while p.divides(N):
            p = primes.next()
        v = vecP(p)
        if verbose:
            print("v={}".format(v))
        A1 = A.stack(vector(v))
        if A1.rank() > A.rank():
            A = A1
            T.append(p)
            if verbose:
                print("new A={} with {} rows and {} cols".format(A,A.nrows(),A.ncols()))
                print("T increases to {}".format(T))
    return T

# Primes for S3 case (as in last chapter of Argaez thesis)

def S3primes(K, S, f, verbose=False):
    """f(x) defines the S3-extension of K
    """
    # First: primes P such that f mod P is irreducible and P is inert
    # in K(sqrt(a)), for each a in K(S,2)/<D> where D=disc(f):

    if verbose:
        print("finding first set of primes")
    KS2, KS2_gens, from_KS2, to_KS2 = pSelmerGroup(K,S,ZZ(2))
    D = f.discriminant()
    quo = KS2 / KS2.subspace([to_KS2(D)])
    alphas = [from_KS2(quo.lift(w)) for w in quo if w]
    if verbose:
        print("alphas = {}".format(alphas))
    alpha_flags = [False for _ in alphas]
    xK = polygen(K)
    quads = [xK**2-alpha for alpha in alphas]
    primes = primes_iter(K,None)
    Ta = Set()
    N = prod(S,1)
    while sum(alpha_flags)<len(alphas):
        p = primes.next()
        while p.divides(N):
            p = primes.next()
        # Now p is a candidate test prime
        if verbose:
            print("testing P={} (have covered {} alphas so far)".format(p,sum(alpha_flags)))
        Fp = residue_field(p)
        while not f.change_ring(Fp).is_irreducible():
            if verbose:
                print("no good, f not irreducible mod p={}".format(p))
            p = primes.next()
            while p.divides(N):
                p = primes.next()
            Fp = residue_field(p)
        if verbose:
            print("P={} passes first test".format(p))
        # p has passed the first criterion: f mod p irreducible
        # p is useful if x^2-alpha irreducible mod p for some alpha
        for i,h in enumerate(quads):
            if not alpha_flags[i]:
                alpha_flags[i] = len(h.roots(Fp))==0
                if alpha_flags[i]:
                    if verbose:
                        print("This p is good for alpha = {}".format(alphas[i]))
                    Ta = Ta.union(Set([p]))
        # Now we try the next prime p, until all alphas are satisfied
    if verbose:
        print("Primes for first test: {}".format(Ta))

    # Second: primes P such that g mod P is irreducible, for each quartic g with cubic resolvent f:
    L = K.extension(f,'b')
    quartics = A4_extensions_with_resolvent(K,S,L)
    Tb = Set()
    primes = primes_iter(K,None)
    quartic_flags = [False for _ in quartics]
    while sum(quartic_flags)<len(quartics):
        p = primes.next()
        while p.divides(N):
            p = primes.next()
        # Now p is a candidate test prime
        Fp = residue_field(p)
        for i,h in enumerate(quartics):
            if not quartic_flags[i]:
                quartic_flags[i] = h.change_ring(Fp).is_irreducible()
                if quartic_flags[i]:
                    Tb = Tb.union(Set([p]))
    if verbose:
        print("Primes for second test: {}".format(Tb))
    T = list(Ta.union(Tb))
    if verbose:
        print("complete set of primes: {}".format(T))
    return T
