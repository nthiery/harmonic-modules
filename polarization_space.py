# -*- coding: utf-8 -*-
"""
Potential user interface::

    sage: P = ...
    sage: generators = ...(mu, nu, ...)
    sage: space = polarizationSpace(P, generators)
    sage: space.character()  # the GL_n character

Variant::

    sage: polarization_character(P, generators)  # Qui en interne appelle polarization_space
"""

load("diagonal_polynomial_ring.py")

def polarizationSpace(P, generators, use_symmetry=False, verbose=False):
    # mu? r? use_symmetry?
    """
    Starting from  polynomials (=generators) in the mu-isotypic component of the polynomial ring in one set of variables (possibly with additional inert variables), construct the space obtained by polarization.

    P: a diagonal polynomial ring (or assymmetric version)
    generators: polynomials in one set of variables (+inert) in the image of b_mu
    """

    S = Subspace(generators=generators,operators=P.polarization_operators_by_degree(),verbose=verbose)
    # add_degree?
