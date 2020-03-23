# T0T1T2.py: code implementing some 2-adic Black Box Galois Representation algorithms

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

# This file contains SageMath code to compute the sets T0, T1 and T2
#  as defined in Argaez and Cremona "Black Box Galois Representations"
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

def lamvec(f,plist, la=lam):
    return [la(f,p) for p in plist]

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
       if p==2:
          continue
       if K==QQ:
            yield p
       else:
            for P in K.primes_above(p,degree):
                yield P

# return a prime (of degree 1) not dividing N modulo which f is
# irreducible, over the field K.  Return 0 if none is found.

def get_p_1(K,f,N,la=lam):
   discf = f.discriminant()
   for p in primes_iter(K):
      if not p.divides(N) and not p.divides(discf) and la(f,p):
         return p
   return 0

# return a prime not dividing N modulo which exactly one of f,g is
# irreducible (or 0 if none found):

def get_p_2(K,f,g,N, la=lam):
   fden = f.denominator()
   gden = g.denominator()
   ff = fden*f
   gg = gden*g
   discf = ff.discriminant()
   discg = gg.discriminant()
   bad = N*discf*discg*fden*gden
   for p in primes_iter(K):
      if (not p.divides(bad)) and (la(f,p)!=la(g,p)):
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
      from C2C3S3 import C3S3_extensions
      flist = C3S3_extensions(K,S)
   if verbose:
      print("cubics: {}".format(flist))

# Append the reducible cubic
   x = polygen(K)
   flist0 = flist + [x**3]
   n = len(flist)

# Starting with no primes, compute the lambda matrix
   plist = []
   vlist = [lamvec(f,plist) for f in flist0]
   ij = equal_vecs(vlist)
   if verbose:
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
      if verbose:
         print("With plist={}, vlist={}, ij={}".format(plist,vlist,ij));
   vlist = vlist[:-1]

   # Sort the primes into order and recompute the vectors:
   plist.sort()
   vlist = [lamvec(f,plist) for f in flist]
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
      return ((1-ZZ(D).kronecker(p))//2) % 2

   # Otherwise we retrieve the field K (here p may be a prime ideal or a prime element)
   try:
      K = p.ring()
   except AttributeError:
      K = p.parent()

   # and count how many primes in K lie above p:
   x = polygen(K)
   L = K.extension(x**2-D,'b')
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
   from KSp import IdealGenerator
   Sx = [IdealGenerator(P) for P in S]
   if unit_first:
      Sx = [u] + Sx
   else:
      Sx = Sx + [u]
   r = len(Sx)
   N = prod(S,1)
# Initialize T1 to be empty and A to be a matric with 0 rows and r=#Sx columns
   T1 = []
   A = Matrix(GF(2),0,len(Sx))
   primes = primes_iter(K,1)
   p = next(primes)
# Repeat the following until A has full rank: take the next prime p
# from the iterator, skip if it divides N (=product over S), form the
# vector v, and keep p and append v to the bottom of A if it increases
# the rank:
   while A.rank() < r:
      p = next(primes)
      while p.divides(N):
         p = next(primes)
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

   # the last thing returned is a "decoder" which returns the
   # discriminant Delta given the splitting beavious at the primes in
   # T1:
   B = A.inverse()
   def decoder(alphalist):
      e = list(B*vector(alphalist))
      return prod([D**ZZ(ei) for D,ei in zip(Sx,e)], 1)

   return T1, A, decoder

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
   from KSp import IdealGenerator
   Sx = [IdealGenerator(P) for P in S]
   if unit_first:
      Sx = [u] + Sx
   else:
      Sx = Sx + [u]
   r = len(Sx)
   r2 = r*(r-1)//2
   N = prod(S,1)
   T2 = {}
   primes = primes_iter(K,1)
   p = next(primes)
   while len(T2)<r+r2:
      p = next(primes)
      while p.divides(N):
         p = next(primes)
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

###############################################################

# We have not implemented a class in Sage for general Black Box Galois
# Representations, though it would be good to do so, allowing as input
# an elliptic curve or a suitable modular form, taking S to be the
# support of the conductor or level and have the traces returned be
# either Traces of Frobenius for an elliptic curve or Hecke
# eigenvalues for a modular form.  One day we will.

# To simulate a Black Box for the examples, all we need is a function
# which returns a monic quadratic (characteristic polynomial of
# Frobenius) on being given a prime.  We can construct such a function
# easily from an elliptic curve. (This will raise an error if given a
# prime of bad reduction.)

def BlackBox_from_elliptic_curve(E):
   return lambda p: E.reduction(p).frobenius_polynomial()

def BB_trace(BB):
   return lambda p: -BB(p)[1]

def BB_det(BB):
   return lambda p: BB(p)[0]

def BB_t0(BB):
   return lambda p: BB(p)(1)%2

def BB_t1(BB):
   return lambda p: (BB(p)(1)//2)%2

def BB_t2(BB):
   return lambda p: (BB(p)(1)//4)%2

def BB_t4(BB):
   return lambda p: (BB(p)(1)//16)%2



#############################################################################
#                                                                           #
# Implementation of Algorithm 6 (page 22) for an elliptic curve Black Box   #
#                                                                           #
#############################################################################

# This function takes as input a dictionary with values in GF(2) and
# keys all singletons{i} and doubletons {i,j} with i,j in range(n),
# and returns
#
# *either* two nonzero vectors x, y in GF(2)^n such that the
# dictionary values are x[i]*y[i] and (x[i]+x[j])*(y[i]+y[j]),
#
# *or* 0 if the only solutions have x=0 or y=0.

def solve_vectors(n,d, verbose=False):
   def w(i,j):
      return 0 if i==j else (d[Set([i,j])] + d[Set([i])] + d[Set([j])])
   W = Matrix(GF(2),[[w(i,j) for j in range(n)] for i in range(n)])
   v = vector(GF(2),[d[Set([i])] for i in range(n)])
   if verbose:
      print("W = {}".format(W))
      print("v = {}".format(v))
   if W==0:
      if v==0:
         return 0
      else:
         return v, v

   Wrows = [wr for wr in W.rows() if wr]
   if v==0:
      x = Wrows[0]
      y = next(wr for wr in Wrows[1:] if wr!=x)
      return x, y

   z = W.row(v.support()[0])
   y = next(wr for wr in Wrows if wr!=z)
   return y+z, y

# Function which maps a GF(2)-vector of exponents to the corresponding discriminant:

def vec_to_disc(basis, exponents):
   return prod([D for D,c in zip(basis,list(exponents)) if c])

# The following function takes as in put S and Black Box (assumed to
# have reducible residual representation, i.e. BB(P)(1)=0 (mod 2) for
# all P not in S), and returns
#
# either: False (if the BT tree is large)
# or: Dx, Dy (if the BT tree is small with vertex discriminants Dx, Dy)

def algo6(K,S,BB, T2=None, unit_first = True, verbose=False):
   r = 1+len(S)
   if T2 is None:
      T2 = get_T2(K,S, unit_first)
      if verbose:
         print("T2 = {}".format(T2))
   assert len(T2)==r*(r+1)//2

   from KSp import IdealGenerator
   Sx = [IdealGenerator(P) for P in S]
   u = -1 if K==QQ else  K(K.unit_group().torsion_generator())
   Sx = [u] + Sx if unit_first else Sx+[u]
   if verbose:
      print("Basis for K(S,2): {}".format(Sx))

   ap = BB_trace(BB)
   apdict = dict((k,ap(T2[k])) for k in T2)
   t1 = BB_t1(BB)
   t1dict = dict((k,t1(T2[k])) for k in T2)
   if verbose:
      print("apdict = {}".format(apdict))
      print("t1dict = {}".format(t1dict))

   s = solve_vectors(r, t1dict)
   if not s:
      return False
   x, y = s
   if verbose:
       print("x = {}".format(x))
       print("y = {}".format(y))

   Dx = vec_to_disc(Sx, x)
   Dy = vec_to_disc(Sx, y)
   if verbose:
      print("Delta_x = {}".format(Dx))
      print("Delta_y = {}".format(Dy))
   return Dx, Dy

# The following are not yet general.  We implement section 6.3
# (trivial det mod 2^{k+1}) only for k=1, as required for Examples 2
# and 3, and section 6.4 (nontrivial det mod 2^{k+1}) only for k=2, as
# required for Example 3.

def algo63(K, S, BB, T2=None, unit_first = True, verbose=False):
   r = 1+len(S)
   if T2 is None:
      T2 = get_T2(QQ,S, unit_first)
      if verbose:
         print("T2 = {}".format(T2))
   assert len(T2)==r*(r+1)//2

   from KSp import IdealGenerator
   Sx = [IdealGenerator(P) for P in S]
   u = -1 if K==QQ else  K(K.unit_group().torsion_generator())
   Sx = [u] + Sx if unit_first else Sx+[u]
   if verbose:
      print("Basis for K(S,2): {}".format(Sx))

   BBdict = dict((k,BB(T2[k])) for k in T2)
   ap = BB_trace(BB)
   apdict = dict((k,ap(T2[k])) for k in T2)
   t2 = BB_t2(BB)
   t2dict = dict((k,t2(T2[k])) for k in T2)
   if verbose:
      print("apdict = {}".format(apdict))
      print("t2dict = {}".format(t2dict))

   v = vector(GF(2),[t2dict[Set([i])] for i in range(r)])
   if verbose:
      print("v = {}".format(v))

   def w(i,j):
      if i==j:
         return 0
      else:
         return (t2dict[Set([i,j])] + t2dict[Set([i])] + t2dict[Set([j])])

   W = Matrix(GF(2),[[w(i,j) for j in range(r)] for i in range(r)])
   rkW = W.rank()
   if verbose:
      print("W = \n{} with rank {}".format(W,rkW))
   # Case 1: rank(W)=2
   if rkW==2:
      # x and y are any two distinct nonzero rows of W
      Wrows = [wr for wr in W.rows() if wr]
      x = Wrows[0]
      y = next(wr for wr in Wrows if wr!=x)
      z = x+y
      u = v - vector(xi*yi for xi,yi in zip(list(x),list(y)))
      if verbose:
         print("x = {}".format(x))
         print("y = {}".format(y))
         print("z = {}".format(z))
         print("u = {}".format(u))
   else: # W==0
      # y=0, x=z
      u = v
      y = u-u # zero vector
      if verbose:
         print("u = {}".format(u))
         print("y = {}".format(y))
      t3dict = {}
      for k in T2:
         t = 1 if t2dict[k]==0 else -1
         t3dict[k] = (BBdict[k](t)//8)%2
      s = solve_vectors(r,t3dict)
      if not s:
         z = x = y # = 0
         if verbose:
            print("x and  y are both zero, so class has >4 vertices")
      else:
         x, _ = s
         z = x
         if verbose:
            print("x = {}".format(x))
            print("y = {}".format(y))
            print("z = {}".format(z))

   return [vec_to_disc(Sx,vec) for vec in [u,x,y,z]]

def algo64(K, S, BB, T2=None, unit_first = True, verbose=False):
   r = 1+len(S)
   if T2 is None:
      T2 = get_T2(QQ,S, unit_first)
      if verbose:
         print("T2 = {}".format(T2))
   assert len(T2)==r*(r+1)//2

   from KSp import IdealGenerator
   Sx = [IdealGenerator(P) for P in S]
   u = -1 if K==QQ else  K(K.unit_group().torsion_generator())
   Sx = [u] + Sx if unit_first else Sx+[u]
   if verbose:
      print("Basis for K(S,2): {}".format(Sx))

   #BBdict = dict((k,BB(T2[k])) for k in T2)
   ap = BB_trace(BB)
   apdict = dict((k,ap(T2[k])) for k in T2)
   t4 = BB_t4(BB)
   t4dict = dict((k,t4(T2[k])) for k in T2)
   if verbose:
      print("apdict = {}".format(apdict))
      print("t4dict = {}".format(t4dict))

   v = vector(GF(2),[t4dict[Set([i])] for i in range(r)])
   if verbose:
      print("v = {}".format(v))

   def w(i,j):
      if i==j:
         return 0
      else:
         return (t4dict[Set([i,j])] + t4dict[Set([i])] + t4dict[Set([j])])

   # Note that W ignores the first coordinate
   Wd = Matrix(GF(2),[[w(i,j) for j in range(1,r)] for i in range(1,r)])
   vd = vector(v.list()[1:])
   rkWd = Wd.rank()
   if verbose:
      print("W' = \n{} with rank {}".format(Wd,rkWd))
   # Case 1: rank(W)=2
   if rkWd==2:
      # x' and y' are any two distinct nonzero rows of W
      Wrows = [wr for wr in Wd.rows() if wr]
      xd = Wrows[0]
      yd = next(wr for wr in Wrows if wr!=xd)
      zd = xd+yd
      ud = vd - vector(xi*yi for xi,yi in zip(list(xd),list(yd)))
      if verbose:
         print("x' = {}".format(xd))
         print("y' = {}".format(yd))
         print("z' = {}".format(zd))
         print("u' = {}".format(ud))
         print("v' = {}".format(vd))

      u = vector([1]+ud.list())
      v = vector([0]+vd.list())

      if t4dict[Set([0])]==1:
         x = vector([1]+xd.list())
         y = vector([1]+yd.list())
         z = vector([1]+zd.list())
         if verbose:
            print("x = {}".format(x))
            print("y = {}".format(y))
            print("z = {}".format(z))
            print("u = {}".format(u))
            print("v = {}".format(v))
      else:
         raise NotImplementedError("t_4(p_1) case not yet implemented in algo64")

      return [vec_to_disc(Sx,vec) for vec in [u,x,y,z]]

   # W==0
   raise NotImplementedError("rank(W)=0 case not yet implemented in algo64")

