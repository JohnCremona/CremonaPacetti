# Sagemath code to compute the sets T0, T1 and T2 as defined in
#  Cremona and Argaez "Black Box Galois Representations"
#
# Requires the file C2C3S3.py from which the function
# C3S3_extensions() is imported, and that file requires KSp.py
#

from sage.all import GF, Primes, QQ, prod, polygen, ZZ, vector, Set, Matrix

# Return the residue field at p uniformly for p a prime number or a
# prime ideal

def residue_field(p):
   try:
      return GF(p)
   except TypeError:
      return p.residue_field()

# The function lamda(f,p) of Definition 4.1

def lam(f,p):
   return int(len(f.roots(residue_field(p)))==0)

# Vector version of lambda over a list of primes

def lamvec(f,plist):
    return [lam(f,p) for p in plist]

# Given a vector (list) vv, return a pair of indices i<j with
# vv[i]==vv[j], or return 0 if the entries are distinct:

def equal_vecs(vv):
    n = len(vv)
    for i in range(n):
        for j in range(i+1,n):
            if vv[i]==vv[j]:
                return [i,j]
    return 0

# Iterator over either primes (K=QQ) or prime ideals.  By default only
# degree 1 primes are returned.

def primes_iter(K, degree=1):
    for p in Primes():
        if K==QQ:
            yield p
        else:
            for P in K.primes_above(p,degree):
                yield P

# return a prime (of degree 1) not dividing N modulo which f is
# irreducible, over the field K.  Return 0 if none is found.

def get_p_1(K,f,N):
    for p in primes_iter(K):
        if not p.divides(N) and lam(f,p):
            return p
    return 0

# return a prime not dividing N modulo which exactly one of f,g is
# irreducible (or 0 if none found):

def get_p_2(K,f,g,N):
    for p in primes_iter(K):
        if not p.divides(N) and lam(f,p)!=lam(g,p):
            return p
    return 0

###########################################
#                                         #
# Compute T0, a distinguishing set for S  #
#                                         #
# Implementation of Algorithm 2, page 12  #
#                                         #
###########################################

# Optionally, supply a list of cubics unramified outside S, if known or
# precomputed.  Otherwise the list will be found using the function
# C3S3_extensions().
#
# Returns a triple flist, plist, vlist where
#
# flist is the list of cubics
# plist is the set T0
# vlist is the list of lambda vectors
#

def get_T0(K,S, flist=None, verbose=False):
   # Compute all cubics unramified outside S if not supplied:
   if flist == None:
      from C2C3S3.py import C3S3_extensions
      flist = C3S3_extensions(K,S)
   if verbose:
      print("cubics: {}".format(flist))

# Append the reducible cubic
   x = polygen(K)
   flist0 = flist + [x^3]
   n = len(flist)

# Starting with no primes, compute the lambda matrix
   plist = []
   vlist = [lamvec(f,plist) for f in flist0]
   ij = equal_vecs(vlist)
   print("With plist={}, vlist={}, ij={}".format(plist,vlist,ij));
   N = prod(S,1)
# As long as the vectors in vlist are not all distinct, find two
# indices i,j for which they are the same and find a new prime which
# distinguishes these two, add it to the list and update:
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

#################################################
#                                               #
# Compute T1, a linearly independent set for S  #
#                                               #
# Implementation of Algorithm 1 (page 8)        #
#                                               #
#################################################

# Implementation of the additive character alpha (page 7, after (3))

def alpha(p,D):
   """
   Return 1 if p is inert in K(sqrt(D)), 0 if p splits
   """
   # Over Q we just compute the kronecker symbol, returning 0 if it
   # equals 1 and 1 if it equals -1:
   if p in ZZ:
      return ((1-D.kronecker(p))//2) % 2

   # Otherwise we retrieve the field K (here p may be a prime ideal or a prime element)
   try:
      K = p.ring()
   except AttributeError:
      K = p.parent()

   # and count how many primes in K lie above p:
   x = polygen(K)
   L = K.extension(x^2-D,'b')
   return 2-len(L.primes_above(p))

# Vector version of alpha, over a list of D's:

def alphalist(p, Dlist):
    return [alpha(p,D) for D in Dlist]

# The main function:
#
# K is the field, S the set of primes
#
# Here, for simplicity, we assume that K has class number 1 (as in the
# examples in the paper), so all primes in S are principal and the
# class group is trivial.  Otherwise we could use K.selmer_group(S,2).
# To match the examples in the paper exactly we allow the unit
# generator of K(S,2) to go first or last.

# Returns both T1 and the matrix A

def get_T1(K, S, unit_first=True, verbose=False):
# Sx is a list of generators of K(S,2) with the unit first or last, assuming h(K)=1
   u = -1 if K==QQ else  K(K.unit_group().torsion_generator())
   if unit_first:
      Sx = [u] + [P.gens_reduced()[0] for P in S]
   else:
      Sx = [P.gens_reduced()[0] for P in S] + [u]
   r = len(Sx)
   N = prod(S,1)
# Initialize T1 to be empty and A to be a matric with 0 rows and r=#Sx columns
   T1 = []
   A = Matrix(GF(2),0,len(Sx))
   primes = primes_iter(K,1)
   p = primes.next()
# Repeat the following until A has full rank: take the next prime p
# from the iterator, skip if it divides N (=product over S), form the
# vector v, and keep p and append v to the bottom of A if it increases
# the rank:
   while A.rank() < r:
      p = primes.next()
      while p.divides(N):
         p = primes.next()
      if verbose:
         print("A={} with {} rows and {} cols".format(A,A.nrows(),A.ncols()))
      v = vector(alphalist(p, Sx))
      if verbose:
         print("v={}".format(v))
      A1 = A.stack(v)
      if A1.rank() > A.rank():
         A = A1
         T1 = T1 + [p]
         if verbose:
            print("new A={} with {} rows and {} cols".format(A,A.nrows(),A.ncols()))
            print("T1 increases to {}".format(T1))
   return T1, A

######################################################
#                                                    #
# Compute T2, a quadratically independent set for S  #
#                                                    #
# Implementation of Algorithm 5 (page 20)            #
#                                                    #
######################################################

# For later convenience the returned object is a dictionary whose keys
# are subsets I of size 1 or 2 of {1,2,...,r}, and values the primes
# P_I.

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
      # Compute the values alpha_p(Delta) for Delta in Sx:
      ro = alphalist(p,Sx)
      # Compute the set I(P) of i for which alpha_p(Delta_i)=1:
      ij = Set([i for i,vi in enumerate(ro) if vi])
      if verbose:
         print("P={}, I(P)={}".format(p,ij))
      # Keep I(p) and p if #I(p)=1 or 2 and it's a new subset@
      if len(ij) in [1,2] and not ij in T2:
         T2[ij] = p
   return T2

# Test functions t1 and t2 for the Black Box associated to an elliptic curve E over Q

def t1(E,p):
    return (1+p-E.ap(p))//2 % 2

def t2(E,p):
    return (1+p-E.ap(p))//4 % 2

#############################################################################
#                                                                           #
# Implementation of Algorithm 6 (page 22) for an elliptic curve Black Box   #
#                                                                           #
#############################################################################

# We have not implemented a class in Sage for general Black Box Galois
# Representations, though it would be good to do so, allowing as input
# an elliptic curve or a suitable modular form, taking S to be the
# support of the conductor or level and have the traces returned be
# either Traces of Frobenius for an elliptic curve or Hecke
# eigenvalues for a modular form.  One day we will.

# Meanwhile, the following function takes as in put S and an elliptic
# curve E with 2-torsion, and returns
#
# either: False (if the BT tree is large)
# or: Dx, Dy (if the BT tree is small with vertex discriminants Dx, Dy)

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

