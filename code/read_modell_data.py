from sage.all import ZZ, nth_prime

"""Functions to read output from modell_new (code in
https://github.com/sanni85/Mod-l-galois-representations/tree/master/code/mfmodell)

Format of each line of output (produced by the function data_output():

 ":".join([label, N,k,c,id, dim, ell, index, chi_mod_ell, ap])

where

label=N.k.c.id (N=level, k=weight, c=character (letter code), id=newform (letter code)
  is the label of the characteristic 0 newform
dim = dimension of the newform = degree of its Hecke field
ell = the prime
index = n if this is the n'th occurrence of this ap mod ell vector
chi_mod_ell = list of [x,chi(x) mod ell] x runs through integers generating (Z/NZ)^*
ap = comma-separated list of (ap mod ell), values in 0..ell-1.

e.g. (trivial character)
11.2.a.a:11:2:a:a:1:5:1:[]:3,4,1,3,1,4,3,0,4,0,2,3,2,4,3,4,0,2,3,2,4,0,4,0,3

e.g. (nontrivial character with nontrivial reduction)
16.2.e.a:16:2:e:a:2:5:1:[[5,3],[15,1]]:1,2,1,4,4,2,3,4,3,4,2,2,0,0,3,0,3,3,0,0,3,0,2,2,3

e.g. (nontrivial character with trivial reduction)
19.2.e.a:19:2:e:a:6:3:2:[[2,1]]:0,1,0,2,0,2,0,1,0,0,2,2,0,2,0,0,0,2,2,0,2,2,0,0,2

Note that if the newform has nontrivial character which is trivial
mod ell then the character values will still be listed (they will
all be 1), but if the characteristic zero character is trivial then
the chi_mod_ell field is just []. This is always the case when ell=2 of course.

"""

def read1line(L):
    """
    Parse one in put line and return data as a dict.

    NB There may be several input lines with the same label (when one
    modular form has several mod-ell reductions).  This function only sees
    single lines, so that must be handled by the calling function.

    """
    fields = L.split(":")
    assert len(fields)==10
    chi_list = [] if fields[8]=='[]' else [[int(c) for c in x.split(",")] for x in fields[8][2:-2].split("],[")] # list of [x,chi(x) mod ell]
    ap = [int(ap) for ap in fields[9].split(",")]
    nap = len(ap)
    maxp = nth_prime(nap)
    N = ZZ(fields[1]) # level
    ell = ZZ(fields[6]) # the prime (2 or 3, or we have nothing more implemented)
    Nl = N * (2 if ell==2 else 6)
    S = (Nl).prime_divisors()

    data = {
        'label': fields[0], # label
        'N':     N, # level
        'k':     ZZ(fields[2]), # weight
        'c':     fields[3], # character orbit label suffix letter(s)
        'id':    fields[4], # newform label suffix letter(s)
        'd':     ZZ(fields[5]), # degree of coefficient field
        'ell':   ell, # the prime (2 or 3, or we have nothing more implemented)
        'i':     int(fields[7]), # multiplicity index (see above comments)
        'chi_list':   chi_list,
        'ap':    ap,
        'nap':   nap,
        'maxp':  maxp,
        'S':     S,
        }
    return data

import os
HOME = os.getenv("HOME")
DATA_DIR=os.path.join(HOME, "Mod-l-galois-representations/data/mfmodell")

def read_data(fname, ell, dir=DATA_DIR):
    alldata = []
    filename = "/".join([dir,str(ell),fname])
    label_counter = {} # counts how many times each label has been seen and decorates the label accordingly
    print(f"reading from {filename}")
    for L in open(filename).readlines():
        data = read1line(L)
        if data:
            label = data['label']
            i = label_counter.get(label, 0) + 1
            label_counter[label] = i
            xlabel = "-".join([label, str(i)])
            data['xlabel'] = xlabel
            alldata.append(data)
    return alldata

"""
Below this line are old versions written in 2018 when the data files were from Drew's Magma code

def read1line(L):
    if L[0]!='<':
        return None
    L = L.replace('<','[')
    L = L.replace('>',']')
    L = L.replace(']],',']]')
    L = eval(L)
    assert len(L)==6
    data = {}
    data['N'] = L[0] # level
    data['k'] = L[1] # weight
    data['i'] = L[2] # index of character
    data['d'] = L[3] # degree of coefficient field (=1)
    data['ap'] = dict(L[4])
    data['chilist'] = L[5]
    return data

def read_data(filename='mod-3-reps.txt'):
    alldata = []
    for L in open(filename).readlines():
        data = read1line(L)
        if data:
            alldata.append(data)
    return alldata

# Function to create one line of output in new format

def data_one(ell,data):
    N = data['N']
    k = data['k']
    i = data['i']
    label = ".".join([str(N),str(k),str(i),'?'])
    aps = data['ap']
    ap = ["<{},{}>".format(p,aps[p]) for p in sorted(data['ap'].keys())[:25]]
    return ":".join([label,str(ell)]+ap)

"""
