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


