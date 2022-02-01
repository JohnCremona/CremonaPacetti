# examples.sage: code to compute the examples in the paper "Black Box
#  Galois Representations" by Argaez and Cremona
#
# Adapted 2022-02-01 for Sage versions >= 9.4 which have the K-Selmer group functions built-in.
#
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
# The files C2C3S3.py and T0T1T2.py should be available for
# import (e.g. they should be in the same directory as this).  Start
# Sage from the command line, type the command
#
# %runfile examples.sage
#
# and then follow the instructions.
#

print("To run the examples, type example1() or example2() or example3() at the Sage prompt")

from C2C3S3 import (C3_extensions, S3_extensions)
from T0T1T2 import (get_T0, get_T2, BlackBox_from_elliptic_curve, BB_trace, BB_det, BB_t0, BB_t1, BB_t2, algo6, algo63, algo64)

# The following line means that class groups, etc, are computed
# non-rigorously (assuming GRH) which makes everything run faster.

proof.number_field(False)

def example1(shortcut=True, allcurves=False):
    print("\nExample 1 from page 12:")
    K = QQ
    S = [2,37]
    print("K = {}".format(K))
    print("S = {}".format(S))
    C3s = C3_extensions(K,S)
    print("For K = {} and S = {}, the C3 extension(s) of K unramified outside S are {}".format(K,S,C3s))
    # It takes a couple of seconds to find this cubics, so here we allow a shortcut
    if shortcut:
        x = polygen(QQ)
        S3s = [x^3 - 4*x - 2, x^3 - x^2 - 12*x + 26]
    else:
        S3s = S3_extensions(K,S)
    print("  and the S3 extension(s) of K unramified outside S are {}".format(S3s))
    F = C3s + S3s
    print("Hence we may take F = {}".format(F))
    flist, T0, vlist = get_T0(K,S,F)
    print("A distinguishing set for F is T0={}".format(T0))
    print("The associated lambda vectors are")
    for f,v in zip(F,vlist): print("lambda={} for f={}".format(v,f))

    print("\nExample 1 (continued) from page 14:")
    if CremonaDatabase().largest_conductor() < 10001:
        print("Since you do not have the optional large Cremona database of elliptic curves installed,")
        print("instead of all 156 isogeny classes of elliptic curves of conductor 2^a*37^b, you will only see 57")
    conductors = [2^a*37^b for a in range(9) for b in range(3)]
    # uncomment the following line to simulate not having the large database
    #conductors = [N for N in conductors if N<10000]
    curves = cremona_optimal_curves(conductors)
    print("There are {} isogeny classes of elliptic curves with good reduction outside {}".format(len(list(curves)),S))
    # after counting we must recreate the iterator
    curves = cremona_optimal_curves(conductors)
    divpols = dict([(f,[]) for f in F+["reducible"]])
    # For each curve compute its lambda vector and hence determine residual reducibility or polynomial:
    for E in curves:
        label = E.label()
        BB = BlackBox_from_elliptic_curve(E)
        t0 = BB_t0(BB)
        lam = [t0(p) for p in T0]
        #print("{} has lambda={}".format(label,lam))
        if lam==[0,0]:
            #print("{}: reducible".format(label))
            divpols["reducible"].append(label)
        else:
            f = F[vlist.index(lam)]
            divpols[f].append(label)
            #print("{}: irreducible, {}".format(label,f))

    for f in F:
        # If the large database is not available, one of the possible cubics does not occur
        if f in divpols:
            print("{} classes have irreducible mod-2 Galois representation with splitting field polynomial {}".format(len(divpols[f]),f))
        else:
            print("No classes have irreducible mod-2 Galois representation with splitting field polynomial {}".format(f))
    nreds = len(divpols["reducible"])
    print("{} classes have reducible mod-2 Galois representation".format(nreds))
    #reducible_curves = [EllipticCurve(lab) for lab in divpols["reducible"]]

    print("\nExample 1 (continued) from page 22.  Note that the indexing set here is {}:".format(range(3)))
    KS2_basis = K.selmer_group(S,2)
    print("Basis for K(S,2) = {}".format(KS2_basis))
    T2 = get_T2(K,S,verbose=False)
    print("T2 is as follows:")
    for I in T2:
        print("I = {}: P_I = {}".format(I,T2[I]))
    if allcurves:
        ncurves=nreds
        print("testing the {} reducible cases to see if the classes are small or large".format(nreds))
    else:
        ncurves=10
        print("testing the first {} of {} reducible cases to see if the classes are small or large.   Run example1(allcurves=True) to see all of them.".format(ncurves,nreds))
    for lab in divpols["reducible"][:ncurves]:
        E = EllipticCurve(lab)
        print("{} has torsion order {}".format(lab,E.torsion_order()))
        BB = BlackBox_from_elliptic_curve(E)
        res = algo6(QQ,S,BB,T2)
        if res:
            print("Class {} is small, with discriminants {} (modulo squares)".format(lab,res))
            discs = Set(E2.discriminant().squarefree_part() for E2 in E.isogeny_class())
            print("Check: the curves in the isogeny class have discriminants with square-free parts {}".format(discs))
        else:
            print("Class {} is large".format(lab))

    print("\nExample 1 (continued) from page 31:")
    lab = '43808a'
    # Simulate the Black Box for this curve:
    BB = BlackBox_from_elliptic_curve(EllipticCurve(lab))
    ap = BB_trace(BB)
    BB_values = dict([(p,ap(p)) for p in T2.values()])
    print("Isogeny class {} has these ap for primes in T2: {}".format(lab,BB_values))

def example2(shortcut=True):
    print("\n"+"-"*80)
    print("\nExample 2 from page 34:")
    x = polygen(QQ)
    K = NumberField(x^2+1,'i')
    i = K.gen()
    N = K.ideal(56+2*i)
    S = N.support()
    print("K = {}".format(K))
    print("S = {}".format(S))
    C3s = C3_extensions(K,S)
    print("For K = {} and S = {}, the C3 extension(s) of K unramified outside S are {}".format(K,S,C3s))
    # It takes about 4m to find 5 cubics, so here we allow a shortcut
    if shortcut:
        x = polygen(K)
        S3s = [x^3 + 9*x + 918*i - 3348,
               x^3 + (132*i - 72)*x + 688*i - 3344,
               x^3 + 12*x - 448*i - 432,
               x^3 + (9*i + 252)*x + 1512*i - 54,
               x^3 + (-9*i + 18)*x - 3067999686071442*i + 5303042246606904]
    else:
        S3s = S3_extensions(K,S)
    print("  and the S3 extension(s) of K unramified outside S are {}".format(S3s))
    F = C3s + S3s
    print("Hence we may take F = {}".format(F))
    flist, T0, vlist = get_T0(K,S,F)
    print("A distinguishing set for F is T0={}".format(T0))

    # To simulate the Black Box we use the elliptic curve 2.0.4.1-3140.3-c1
    E = EllipticCurve(K, [i + 1, -i + 1, 0, 62*i - 22, -192*i - 54])
    BB = BlackBox_from_elliptic_curve(E)
    ap = BB_trace(BB)
    # Check for reducibility of the residual representation:
    aps = [ap(P) for P in T0]
    print("The a_P for P in T0 are: {}".format(aps))
    assert all(a%2==0 for a in aps)
    print("All are 0 mod 2, so the mod-2 representation is reducible")

    # Find a quadratically independent set T2:
    T2 = get_T2(K,S, unit_first=False, verbose=False)
    print("T2 is as follows:")
    for I in T2:
        print("I = {}: P_I = {}".format(I,T2[I]))

    t1 = BB_t1(BB)
    t1_values = [t1(P) for P in T2.values()]
    assert all(t1==0 for t1 in t1_values)
    print("F_P(1) = 0 (mod 4) for all P in T2, so the class is large")
    Da, Db, Dc, Dabcd = algo63(K,S,BB,T2,unit_first=False)
    # print("Da = {}".format(Da))
    # print("Db = {}".format(Db))
    # print("Dc = {}".format(Dc))
    # print("Dabcd = {}".format(Dabcd))
    assert Db!=1 and Dc!=1 and Dabcd!=1
    print("The isogeny graph has four vertices, and the extremal discriminants are {}, {}, {} (modulo squares)".format(Db,Dc,Dabcd))
    print("Check against the elliptic curves in isogeny class 2.0.4.1.3140-c:")
    c1 = EllipticCurve(K, [i + 1, -i + 1, 0, 62*i - 22, -192*i - 54])
    print("c1 ={} has discriminant {}".format(c1.ainvs(), c1.discriminant().factor()))
    c2 = EllipticCurve(K, [i + 1, -1, 0, -48*i + 18, 30*i - 158])
    print("c2 ={} has discriminant {}".format(c2.ainvs(), c2.discriminant().factor()))
    c3 = EllipticCurve(K, [i + 1, -1, 0, 7*i + 8, 10*i - 18])
    print("c3 ={} has discriminant {}".format(c3.ainvs(), c3.discriminant().factor()))
    c4 = EllipticCurve(K, [0, -i + 1, 0, -30*i - 36, -102*i - 85])
    print("c4 ={} has discriminant {}".format(c4.ainvs(), c4.discriminant().factor()))


def example3(shortcut=True):
    print("\n"+"-"*80)
    print("\nExample 3 from page 35:")
    x = polygen(QQ)
    K = NumberField(x^2+1,'i')
    i = K.gen()
    N = K.ideal(10+10*i)
    S = N.support()
    print("K = {}".format(K))
    print("S = {}".format(S))
    C3s = C3_extensions(K,S)
    print("For K = {} and S = {}, the C3 extension(s) of K unramified outside S are {}".format(K,S,C3s))
    # It takes about 11s to find one cubic, so here we allow a shortcut
    if shortcut:
        x = polygen(K)
        S3s = [x^3 - 15*x - 70*i]
    else:
        S3s = S3_extensions(K,S)
    print("  and the S3 extension(s) of K unramified outside S are {}".format(S3s))
    F = C3s + S3s
    print("Hence we may take F = {}".format(F))
    flist, T0, vlist = get_T0(K,S,F)
    print("A distinguishing set for F is T0={}".format(T0))

    # To simulate the Black Box we use the elliptic curve 2.0.4.1-200.2-a1 (which is isogenous to a base change of 40.a3/Q)
    E = EllipticCurve(K, [i + 1, i, i + 1, -31*i - 44, 94*i + 106])
    BB = BlackBox_from_elliptic_curve(E)
    ap = BB_trace(BB)
    # Check for reducibility of the residual representation:
    aps = [ap(P) for P in T0]
    print("The a_P for P in T0 are: {}".format(aps))
    assert all(a%2==0 for a in aps)
    print("All are 0 mod 2, so the mod-2 representation is reducible")

    # Find a quadratically independent set T2:
    T2 = get_T2(K,S, unit_first=True, verbose=False)
    print("T2 is as follows:")
    for I in T2:
        print("I = {}: P_I = {}".format(I,T2[I]))

    t1 = BB_t1(BB)
    t1_values = [t1(P) for P in T2.values()]
    assert all(t1==0 for t1 in t1_values)
    print("F_P(1) = 0 (mod 4) for all P in T2, so the class is large")
    Da, Db, Dc, Dabcd = algo63(K,S,BB,T2, unit_first=True, verbose=True)
    assert Da==1 and Db==1 and Dc==1 and Dabcd==1
    print("The isogeny graph has more than four vertices, and the mod 4 representation is trivial")

    Da, Db, Dc, Dabcd = algo64(K,S,BB,T2, unit_first=True, verbose=True)
    assert Da!=1 and Db!=1 and Dabcd!=1 and Da!=1
    print("Da = {}".format(Da))
    print("Db = {}".format(Db))
    print("Dc = {}".format(Dc))
    print("Dabcd = {}".format(Dabcd))
    print("The isogeny graph has 10 vertices, four inner ones of degree 3, and 3 pairs of extremal ones with discriminants {}, {}, {}".format(Db,Dc,Dabcd))
    print("The extra discriminant is {}".format(Da))
    print("The image of the mod 8 representation has order 16 and its kernel is the multiquadratic extension obtained by adjoining all four of these discriminants.")

