#import datetime
#from compute_character import *

#t1 = datetime.datetime.now()
#E = E_mu(Partition([2,2,2]), parallel=True)
#t2 = datetime.datetime.now()
#print t2-t1

#t1 = datetime.datetime.now()
#E = E_mu(Partition([2,2,2]), parallel=False)
#t2 = datetime.datetime.now()
#print t2-t1

def sans_opti(mu):
    n = mu.size()
    r = n-1
    v = vandermonde(mu, r)
    op = [e for l in partial_derivatives(v.parent()).itervalues() for e in l]
    op += [e for l in polarization_operators(r, max_deg=r).itervalues() for e in l]
    E = Subspace(generators = [v], operators = op)
    return E.basis()

def opti1(mu):
    n = mu.size()
    r = n-1
    v = vandermonde(mu, r)
    deriv = [e for l in partial_derivatives(v.parent()).itervalues() for e in l]
    pol = [e for l in polarization_operators(r, max_deg=r).itervalues() for e in l]
    E1 = Subspace(generators = [v], operators = deriv)
    gen2 = [g for g in E1.basis()[0]]
    E2 = Subspace(generators = gen2, operators = pol)
    return E2.basis()


def opti2(mu):
    n = mu.size()
    r = n-1
    v = vandermonde(mu, r)
    deriv = [e for l in partial_derivatives(v.parent()).itervalues() for e in l]
    pol = [e for l in polarization_operators(r, max_deg=r).itervalues() for e in l]
    E1 = Subspace(generators = [v], operators = deriv)
    E2 = IsotypicComponent(E1, n)
    E3 = []
    if n==1:
        gen = [e for l in E2.basis().values() for e in l]
        E3 += [[Subspace(gen, pol).basis()]]
    else :
        for S in E2.itervalues():
            gen = [e for l in S.basis().values() for e in l]
            E3 += [[Subspace(gen, pol).basis()]]
    return E3
        

def opti3(mu):
    n = mu.size()
    r = n-1
    v = vandermonde(mu)
    E1 = Subspace({v.multidegree():[v]}, partial_derivatives(v.parent()))
    E2 = IsotypicComponent(E1, n)
    E3 = PolarizedSpace(E2, polarization_operators(r, max_deg=r))
    if n==1:
        return E3.basis()
    else:
        res = [S.basis() for S in E3.itervalues()]
        return E3

def test3(mu):
    E = test2(mu)
    return character(E)
