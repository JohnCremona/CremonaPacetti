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

def primes_iter(K, degree=1, N=1):
    for p in Primes():
        if N%p==0:
            continue # skip to next p
        if K==QQ:
            yield p
        else:
            print("testing p={}".format(p))
            for P in K.primes_above(p,degree):
                yield P

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
    primes = primes_iter(K,None, N.norm()*K.defining_polynomial().discriminant().norm())
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
        Wrows = [w for w in Wrows if w]
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

