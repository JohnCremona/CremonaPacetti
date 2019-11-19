## Polynomial utility functions

from sage.all import QQ, pari, PolynomialRing

def sagepol(paripol, var='x'):
    """Convert a pari polynomial in QQ[x] from sage.  The variable in
    paripol must match the string var (default: 'x'), and the result
    will be a Sage polynomial with the same variable name.
    """
    Qx = PolynomialRing(QQ,var)
    return paripol.sage({var:Qx.gen()})

def polredabs(pol):
    """Use Pari's polredabs to simplify a polynomial in Q[x].  The
    variable name does not have to be x.
    """
    x = pol.parent().variable_name()
    return sagepol(pari(pol).polredabs(), x)

def polredbest(pol):
    """Use Pari's polredbest to simplify a polynomial in Q[x].  The
    variable name does not have to be x.

    This is faster than polredabs, especially if the polynomial
    defines a number field with many subfields, but the result is not
    canonical.
    """
    x = pol.parent().variable_name()
    return sagepol(pari(pol).polredbest(), x)

def polredbest_stable(pol):
    """Use Pari's polredbest repeatedly (until there is no change) to
    simplify a polynomial in Q[x].  The variable name does not have to
    be x.

    This is faster than polredabs, especially if the polynomial
    defines a number field with many subfields, but the result is not
    canonical.
    """
    x = pol.parent().variable_name()
    f = pari(pol)
    oldf = None
    while f!=oldf:
        oldf, f = f, f.polredbest()
    return sagepol(f,x)

def rescale(f):
    """Rescale the variable and coefficients to return a monic polynomial
    with integer coefficients with the same root up to multiplcation
    by a constant in the base field.  The base field can be QQ or a
    number field (even relative).
    """
    d = f.denominator()
    if d==1:
	return f
    x = f.parent().gen()
    n = f.degree()
    return d**n*f(x/d)

def pol_simplify(f, use_polredabs=False, debug=False):
    """Return a simpler polynomial defining the same extension field.

    f should be irreducible in K[x] where K is QQ or a number field.

    If use_polredabs is False (default) the pari's polredbest is used
    (repeatedly until it stabilises), which is faster, otherwise
    pari's polredabs is used.
    """
    K = f.base_ring()
    g = rescale(f)
    if K==QQ:
        return polredabs(g) if use_polredabs else polredbest_stable(g)
    L = K.extension(g,'a_')
    h = pol_simplify(L.absolute_polynomial(), use_polredabs)

    # one factor of h over K will define the same relative extension
    # of K as the original.  We return the first such:
    new_f = (p for p,e in h.change_ring(K).factor() if K.extension(p,'b_').is_isomorphic_relative(L)).next()
    if debug:
        print("{} ---> {}".format(f,new_f))
        assert K.extension(new_f,'b_').is_isomorphic_relative(L)
    return new_f
