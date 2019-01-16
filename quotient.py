#!/usr/bin/env python
# -*- coding: utf-8 -*-

from subspace import *

def quotiented_basis(P, basis, operators):
    """
        INPUT:
            - P -- a polynomial ring
            - basis -- basis of the space to quotient
            - operators -- operators applied to build the quotient
        
        OUTPUT : The basis of the quotiended space
        
        EXAMPLES :
            sage: P = DiagonalPolynomialRing(QQ, 3, 1, inert=1) 
            sage: W = DerivativeVandermondeSpaceWithInert(QQ, Diagram([(0,0),(1,0),(3,0)]))
            sage: basis = W.basis()
            sage: operators = [functools.partial(P.symmetric_derivative, d=[d]) for d in range(1, W.degree_vandermonde()+1)]
            sage: for key,b in quotiented_basis(P, basis, operators).iteritems():
            ....:     print key, b
            ((1,), [3]) (x00 + x01 + x02,)
            ((2,), [2, 1]) (x00^2 - x02^2, -x00*x01 + x01*x02)
            ((3,), [2, 1]) (x00^3 - x00^2*x01 - 2*x00*x01^2 + x00^2*x02 + 2*x01^2*x02 - x00*x02^2 + x01*x02^2 - x02^3,)
            ((4,), [1, 1, 1]) (-x00^3*x01 + x00*x01^3 + x00^3*x02 - x01^3*x02 - x00*x02^3 + x01*x02^3,)

    """
    generators = [P(p) for b in basis.itervalues() for p in b]
    quotient = []
    for op in operators:
         for b in basis.itervalues():
             for p in b:
                 if op(P(p))!=0:
                     quotient += [op(P(p))]
    S = Subspace(quotient, [])
    quotient_basis = S.basis()[0]
    
    new_basis = {}
    for key, b in basis.iteritems():
        new_b = tuple(p for p in b if p not in quotient_basis)
        if new_b != ():
            new_basis[key] = new_b
    return new_basis
