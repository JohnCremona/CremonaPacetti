# Code to compute the sets T0, T1 and T2 as defined in Cremona and
#  Argaez "Black Box Galois Representations"

from sage.all import GF, Primes, QQ, prod, polygen, ZZ, vector, Set, Matrix

def residue_field(p):
   try:
      return GF(p)
   except TypeError:
      return p.residue_field()

def lam(f,p):
   return int(len(f.roots(residue_field(p)))==0)

def lamvec(f,plist):
    return [lam(f,p) for p in plist]

# return indices i<j with vv[i]==vv[j], or 0 if they are distinct:

def equal_vecs(vv):
    n = len(vv)
    for i in range(n):
        for j in range(i+1,n):
            if vv[i]==vv[j]:
                return [i,j]
    return 0

def primes_iter(K, degree=1):
    for p in Primes():
        if K==QQ:
            yield p
        else:
            for P in K.primes_above(p,degree):
                yield P

# return a prime not dividing N modulo which f is irreducible:

def get_p_1(K,f,N):
    for p in primes_iter(K):
        if not p.divides(N) and lam(f,p):
            return p
    return 0

# return a prime not dividing N modulo exactly one of f,g is irreducible:

def get_p_2(K,f,g,N):
    for p in primes_iter(K):
        if not p.divides(N) and lam(f,p)!=lam(g,p):
            return p
    return 0

# Compute T0, a distinguishing set for S:

def get_T0(K,S, flist=None, verbose=False):
    N = prod(S,1)
    if flist == None:
       from C2C3S3.py import C3S3_extensions
       flist = C3S3_extensions(K,S)
    if verbose:
        print("cubics: {}".format(flist))
    x = polygen(K)
    flist0 = flist + [x^3]
    n = len(flist)
    plist = []
    vlist = [lamvec(f,plist) for f in flist0]
    ij = equal_vecs(vlist)
    print("With plist={}, vlist={}, ij={}".format(plist,vlist,ij));
    while ij:
        i,j = ij
        if j==n:
            p = get_p_1(K,flist[i],N)
        else:
            p = get_p_2(K,flist[i],flist[j],N)
        plist = plist + [p]
        if verbose:
            print("plist = {}".format(plist))
        vlist = [lamvec(f,plist) for f in flist0]
        ij = equal_vecs(vlist)
        print("With plist={}, vlist={}, ij={}".format(plist,vlist,ij));
    vlist = vlist[:-1]
    return flist, plist, vlist


# Funtion to compute  a set  T1 of primes linearly independent with respect to S

def alpha(p,D):
    """
    Return 1 if p is inert in K(sqrt(D)), 0 if p splits
    """
    if p in ZZ:
        return ((1-D.kronecker(p))//2) % 2
    try:
        K = p.ring()
    except AttributeError:
        K = p.parent()
    x = polygen(K)
    L = K.extension(x^2-D,'b')
    return 2-len(L.primes_above(p))

def alphalist(p, Dlist):
    return [alpha(p,D) for D in Dlist]

def get_T1(K, S, unit_first=True, verbose=False):
    u = -1 if K==QQ else  K(K.unit_group().torsion_generator())
    if unit_first:
        Sx = [u] + [P.gens_reduced()[0] for P in S]
    else:
        Sx = [P.gens_reduced()[0] for P in S] + [u]
    r = len(Sx)
    N = prod(S,1)
    M = Matrix(GF(2),0,len(Sx))
    T1 = []
    primes = primes_iter(K,1)
    p = primes.next()
    while M.rank() < r:
        p = primes.next()
        while p.divides(N):
            p = primes.next()
        if verbose:
            print("M={} with {} rows and {} cols".format(M,M.nrows(),M.ncols()))
        v = vector(alphalist(p, Sx))
        if verbose:
            print("v={}".format(v))
        M1 = M.stack(v)
        if M1.rank() > M.rank():
            M = M1
            T1 = T1 + [p]
            if verbose:
                print("new M={} with {} rows and {} cols".format(M,M.nrows(),M.ncols()))
                print("T1 increases to {}".format(T1))
    return T1, M

def get_T2(K, S, unit_first=True, verbose=False):
    u = -1 if K==QQ else  K(K.unit_group().torsion_generator())
    if unit_first:
        Sx = [u] + [P.gens_reduced()[0] for P in S]
    else:
        Sx = [P.gens_reduced()[0] for P in S] + [u]
    r = len(Sx)
    r2 = r*(r-1)//2
    N = prod(S,1)
    T2 = {}
    primes = primes_iter(K,1)
    p = primes.next()
    while len(T2)<r+r2:
        p = primes.next()
        while p.divides(N):
            p = primes.next()
        ro = alphalist(p,Sx)
        ij = Set([i for i,vi in enumerate(ro) if vi])
        if verbose:
            print("P={}, I(P)={}".format(p,ij))
        if len(ij) in [1,2] and not ij in T2:
            T2[ij] = p
    return T2

def t1(E,p):
    return (1+p-E.ap(p))//2 % 2

def t2(E,p):
    return (1+p-E.ap(p))//4 % 2

def algo6(S,E):
    print(E.label())
    r = 1+len(S)
    T2 = get_T2(S)
    assert len(T2)==r*(r+1)//2
    print("T2 = {}".format(T2))
    apdict = dict((k,E.ap(T2[k])) for k in T2)
    t1dict = dict((k,t1(E,T2[k])) for k in T2)
    print("apdict = {}".format(apdict))
    print("t1dict = {}".format(t1dict))
    v = vector(GF(2),[t1dict[Set([i])] for i in range(r)])
    print("v = {}".format(v))
    def w(i,j):
        if i==j:
            return 0
        else:
            return (t1dict[Set([i,j])] + t1dict[Set([i])] + t1dict[Set([j])])
    W = Matrix(GF(2),[[w(i,j) for j in range(r)] for i in range(r)])
    print("W = {}".format(W))
    if v==0 and W==0:
        return False
    if W==0:
        x = y = v
    else:
        Wrows = [W.row(i) for i in range(r)]
        Wrows = [wr for wr in Wrows if wr]
        if v==0:
            x = Wrows[0]
            for y in Wrows[1:]:
                if y!=x:
                    break
        else:
            z = W.row(v.support()[0])
            for y in Wrows:
                if y!=z:
                    break
            x = y+z
    print("x = {}".format(x))
    print("y = {}".format(y))
    Sx = [-1] + S
    Dx = prod([D for D,c in zip(Sx,list(x)) if c])
    Dy = prod([D for D,c in zip(Sx,list(y)) if c])
    print("Delta_x = {}".format(Dx))
    print("Delta_y = {}".format(Dy))
    return Dx, Dy

