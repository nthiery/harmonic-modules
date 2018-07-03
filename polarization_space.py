#!/usr/bin/env python
# -*- coding: utf-8 -*-

load("diagonal_polynomial_ring.py")
load("subspace.py")

def polarizationSpace(P, generators, mu, r, use_symmetry=False, verbose=False):
    # mu? r? use_symmetry?
    """
    Starting from  polynomials (=generators) in the mu-isotypic component of the polynomial ring in one set of variables (possibly with additional inert variables), construct the space obtained by polarization.

    P: a diagonal polynomial ring (or assymmetric version)
    generators: polynomials in one set of variables (+inert) in the image of b_mu
    """

    S = Subspace(generators=generators,operators=P.polarization_operators_by_degree(),verbose=verbose)
    # add_degree? 
    
    
