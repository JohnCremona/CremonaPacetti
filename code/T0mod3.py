# T0mod3.py: code implementing some 3-adic Black Box Galois Representation algorithms

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

# This file contains SageMath code to compute the set T0
#  as defined in Sanna and Cremona "3-adic Black Box Galois Representations"
#
# Requires the files C2C3S3.py and S4.py from which the function
# abs_irred_extensions() is imported, and that file requires KSp.py
#

from sage.all import GF, prod, polygen
from T0T1T2 import equal_vecs, lamvec, get_p_1, get_p_2, alpha, alphalist

# The function lamda(f,p) for quartics

def lam3(f,p):
    #print("f={}".format(f))
    if f.degree()<4:
        return 0
    degs = [g.degree() for g,e in f.change_ring(GF(p)).factor()]
    #print("{} mod {} has factors of degree {}: {}".format(f,p,degs,f.change_ring(GF(p)).factor()))
    l = int( degs in [[1,1,1,1],[1,3],[3,1],[4]] )
    if not l:
        assert degs in [[2,2],[1,1,2],[1,2,1],[2,1,1]]
    #print("lam3({}, {}) = {}".format(f,p,l))
    return l

###########################################
#                                         #
# Compute T0, a distinguishing set for S  #
#                                         #
###########################################

# Optionally, supply a list of absolutely irreducible quartics
# unramified outside S, if known or precomputed.  Otherwise the list
# will be found using the function abs_irred_extensions().  Here,
# "absolutely irreducible" means irreducible with Galois group in {S4,
# A4, V4, D4}.
#
# Returns a triple flist, plist, vlist where
#
# flist is the list of quartics
# plist is the set T0
# vlist is the list of lambda vectors
#

def get_T0_mod3(K,S, flist=None, verbose=False):
   # Compute all absolutely irreducible quartics unramified outside S
   # if not supplied:
   if flist == None:
      from S4 import abs_irred_extensions
      flist = abs_irred_extensions(K,S)
   if verbose:
      print("quartics: {}".format(flist))

# Append a poly with lam3=0
   x = polygen(K)
   flist0 = flist + [x**3]
   n = len(flist)

# Starting with no primes, compute the lambda matrix
   plist = []
   vlist = [lamvec(f,plist,lam3) for f in flist0]
   ij = equal_vecs(vlist)
   if verbose:
      print("With plist={}, vlist={}, ij={}".format(plist,vlist,ij));
   N = prod(S,1) * prod([f.discriminant() for f in flist])
# As long as the vectors in vlist are not all distinct, find two
# indices i,j for which they are the same and find a new prime which
# distinguishes these two, add it to the list and update.  The primes
# must not be in S or divide the discriminant of any of the quartics.
   while ij:
      i,j = ij
      if j==n:
         p = get_p_1(K,flist[i],N, lam3)
      else:
         p = get_p_2(K,flist[i],flist[j],N, lam3)
      plist = plist + [p]
      if verbose:
         print("plist = {}".format(plist))
      vlist = [lamvec(f,plist,lam3) for f in flist0]
      ij = equal_vecs(vlist)
      if verbose:
         print("With plist={}, vlist={}, ij={}".format(plist,vlist,ij));
   vlist = vlist[:-1]

   # Sort the primes into order and recompute the vectors:
   plist.sort()
   vlist = [lamvec(f,plist,lam3) for f in flist]
   return flist, plist, vlist
