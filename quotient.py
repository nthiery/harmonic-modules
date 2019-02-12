#!/usr/bin/env python
# -*- coding: utf-8 -*-

from subspace import *
from add_degree import *
        

def quotient_basis(P, basis, operators):
    """
        INPUT:
            - P -- a polynomial ring
            - basis -- basis of the space to quotient
            - operators -- operators applied to build the quotient
        
        OUTPUT : The basis of the quotiended space
        
        EXAMPLES :
            sage: load("diagonal_polynomial_ring.py")
            sage: load("derivative_space.py")
            sage: P = DiagonalPolynomialRing(QQ, 3, 1, inert=1) 
            sage: W = DerivativeVandermondeSpaceWithInert(QQ, Diagram([(0,0),(1,0),(3,0)]))
            sage: basis = W.basis()
            sage: operators = {-d:[functools.partial(P.symmetric_derivative, d=[d])] for d in range(1, W.degree_vandermonde()+1)}
            sage: for key,b in quotient_basis(P, basis, operators).iteritems():
            ....:     print(key)
            ....:     print(b)
                (2,)
                (x00^2 - 2*x00*x01 + 2*x01*x02 - x02^2,)
                (0,)
                (1,)
                (3,)
                (-x00^2*x01 + x00*x01^2 + x00^2*x02 - x01^2*x02 - x00*x02^2 + x01*x02^2,)
                (1,)
                (x00 - x02,)

    """

    quotient = {}
    for key, b in basis.iteritems():
        add_to_quotient = [v(P(p)) for p in b for op in operators.itervalues() for v in op if v(P(p))!=0]
        for q in add_to_quotient:
            deg = P.multidegree(q)
            if deg not in quotient.iterkeys():
                quotient[deg] = [q]
            else:
                quotient[deg] += [q]
    if quotient != {} :
        return Subspace(quotient, {}).basis()
    else :
        return {}  
         
    #new_basis = {}
    #for key, b in basis.iteritems():
    #    new_b = tuple(p for p in b if p not in quotient_basis)
    #    if new_b != ():
    #        new_basis[key] = new_b
    #return new_basis
