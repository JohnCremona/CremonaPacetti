## Polynomial utility functions

from sage.all import QQ, pari, polygen

### Convert a polynomial in QQ[x] from pari to sage

def sagepol(paripol):
    return paripol.sage({'x':polygen(QQ)})

### Over QQ only, apply pari's polredabs:

def polredabs(pol):
    if pol.base_ring()==QQ:
        return sagepol(pari(pol).polredabs())
    else:
        return pol

### return a monic polynomial with integer coefficients ###

def rescale(f):
    d = f.denominator()
    if d==1:
	return f
    x = f.parent().gen()
    n = f.degree()
    return d**n*f(x/d)

### Return a simpler polynomial defining the same field ###

def pol_simplify(f, debug=False):
    K = f.base_ring()
    g = rescale(f)
    if K==QQ:
        return polredabs(g)
    L = K.extension(g,'a_')
    h = pol_simplify(L.absolute_polynomial())
    # one factor of h over K will define the same relative extension
    # of K as the original.  We return the first such:
    new_f = (p for p,e in h.change_ring(K).factor() if K.extension(p,'b_').is_isomorphic_relative(L)).next()
    if debug:
        print("{} ---> {}".format(f,new_f))
        assert K.extension(new_f,'b').is_isomorphic_relative(L)
    return new_f
