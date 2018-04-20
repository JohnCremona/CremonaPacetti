print("To run the examples, type example1() or example2() or example3() at the Sage prompt")

from C2C3S3 import (C3_extensions, S3_extensions)
from T0T1T2 import (get_T0, get_T2, BlackBox_from_elliptic_curve, algo6)
from KSp import Support

# The following line means that class groups, etc, are computed
# non-rigorously (assuming GRH) which makes everything run faster.

proof.number_field(False)

def example1(shortcut=True, allcurves=False):
    print("\nExample 1 from page 12:")
    K = QQ
    S = [2,37]
    print("K = ".format(K))
    print("S = ".format(S))
    C3s = C3_extensions(K,S)
    print("For K = {} and S = {}, the C3 extension(s) of K unramified outside S are {}".format(K,S,C3s))
    # It takes a couple of seconds to find this cubics, so here we allow a shortcut
    if shortcut:
        x = polygen(QQ)
        S3s = [x^3 - x^2 - 12*x + 26]
    else:
        S3s = S3_extensions(K,S)
    print("  and the S3 extension(s) of K unramified outside S are {}".format(S3s))
    F = C3s + S3s
    print("Hence we may take F = {}".format(F))
    flist, T0, vlist = get_T0(K,S,F)
    print("A distinguishing set for F is T0={}".format(T0))
    print("The associated lambda vectors are")
    for f,v in zip(F,vlist): print("f={}:\t(lambda)={}".format(f,v))

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
    divpols = {}
    for E in curves:
        label = E.label()
        a3 = E.ap(3) % 2
        a5 = E.ap(5) % 2
        lam = [a3,a5]
        irred = False
        for f,v in zip(F,vlist):
            if lam==v:
                if f in divpols:
                    divpols[f].append(label)
                else:
                    divpols[f] = [label]
                irred = True
                break
        if not irred:
            if "reducible" in divpols:
                divpols["reducible"].append(label)
            else:
                divpols["reducible"] = [label]
    print(divpols.keys())
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
        BB = BlackBox_from_elliptic_curve(EllipticCurve(lab))
        res = algo6(QQ,S,BB,T2)
        if res:
            print("Class {} is small, with discrinminants {} (modulo squares)".format(lab,res))
            discs = Set(E2.discriminant().squarefree_part() for E2 in E.isogeny_class())
            print("Check: the curves in the isogeny class have discriminants with square-free parts {}".format(discs))
        else:
            print("Class {} is large".format(lab))

    print("\nExample 1 (continued) from page 31:")
    lab = '43808a'
    # Simulate the Black Box for this curve:
    BB = BlackBox_from_elliptic_curve(EllipticCurve(lab))
    ap = lambda P: -BB(P)[1]
    BB_values = dict([(p,ap(p)) for p in T2.values()])
    print("Isogeny class {} has these ap for primes in T2: {}".format(lab,BB_values))

def example2(shortcut=True):
    print("\n"+"-"*80)
    print("\nExample 2 from page 34:")
    x = polygen(QQ)
    K = NumberField(x^2+1,'i')
    i = K.gen()
    N = K.ideal(56+2*i)
    S = Support(N)
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
    BB_ap = lambda P: -BB(P)[1]
    # Check for reducibility of the residual representation:
    aps = [BB_ap(P) for P in T0]
    print("The a_P for P in T0 are: {}".format(aps))
    assert all(ap%2==0 for ap in aps)
    print("All are 0 mod 2, so the mod-2 representations is reducible")

    # Find a quadratically independent set T2:
    T2 = get_T2(K,S,verbose=False)
    print("T2 is as follows:")
    for I in T2:
        print("I = {}: P_I = {}".format(I,T2[I]))

    BB_t1 = lambda P: BB(P)(1)
    t1_values = [BB_t1(P) for P in T2.values()]
    print("Evaluate F_P(1) for P in T2: {}".format(t1_values))
    assert all(t1%4==0 for t1 in t1_values)
    print("-- all are 0 (mod 4), so the class is large")

def example3(shortcut=True):
    print("\n"+"-"*80)
    print("\nExample 3 from page 35:")
    x = polygen(QQ)
    K = NumberField(x^2+1,'i')
    i = K.gen()
    N = K.ideal(10+10*i)
    S = Support(N)
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
    BB_ap = lambda P: -BB(P)[1]
    # Check for reducibility of the residual representation:
    aps = [BB_ap(P) for P in T0]
    print("The a_P for P in T0 are: {}".format(aps))
    assert all(ap%2==0 for ap in aps)
    print("All are 0 mod 2, so the mod-2 representations is reducible")

    # Find a quadratically independent set T2:
    T2 = get_T2(K,S,verbose=False)
    print("T2 is as follows:")
    for I in T2:
        print("I = {}: P_I = {}".format(I,T2[I]))

    BB_t1 = lambda P: BB(P)(1)
    t1_values = [BB_t1(P) for P in T2.values()]
    print("Evaluate F_P(1) for P in T2: {}".format(t1_values))
    assert all(t1%4==0 for t1 in t1_values)
    print("-- all are 0 (mod 4), so the class is large")

