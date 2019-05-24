#!/usr/bin/env python
# -*- coding: utf-8 -*-

from sage.structure.unique_representation import UniqueRepresentation
from sage.categories.isomorphic_objects import IsomorphicObjectsCategory
from sage.structure.element_wrapper import ElementWrapper
from sage.categories.homset import Hom
from sage.categories.morphism import SetMorphism
from sage.categories.algebras import Algebras
from sage.structure.parent import Parent


# Stuff here everything currently missing in SageMath about isomorphic algebras
class Algebras_IsomorphicObjects(IsomorphicObjectsCategory):
    class ParentMethods:
        def summation(self, x, y):
            return self.retract(x.lift() + y.lift())
        def gens(self):
            return [self.retract(g) for g in self.ambient().gens()]
        def is_field(self):
            return self._ambient.is_field()
        def is_integral_domain(self):
            return self._ambient.is_integral_domain()
        def is_commutative(self):
            return self._ambient.is_commutative()
            
    class ElementMethods:
        def _sub_(x, y):
            return x.parent().retract(x.lift() - y.lift())
        def _neg_(self):
            return self.parent().retract(-self.lift())
        def _div_(x, y):
            return x.parent().retract(x.lift()/y.lift())

Algebras.IsomorphicObjects = Algebras_IsomorphicObjects

class IsomorphicObject(UniqueRepresentation, Parent):
    def ambient(self):
        return self._ambient
    def lift(self, p):
        return p.value
    def retract(self, p):
        return self.element_class(self,p)
    def base_ring(self):
        return self.ambient().base_ring()
    def __init__(self, ambient, category):
        self._ambient = ambient
        Parent.__init__(self, category=category.IsomorphicObjects())
        # Bricolage
        self._remove_from_coerce_cache(ambient)
        phi = SetMorphism(Hom(ambient, self, category), self.retract)
        phi.register_as_coercion()

    class Element(ElementWrapper):
        pass
        

"""
sage: P = PolynomialRing(QQ, ['x','y'])
sage: PP = IsomorphicObject(P, Algebras(QQ))
sage: x,y = PP.gens() 
sage: (2*x + y)^2 + 1
4*x^2 + 4*x*y + y^2 + 1
"""
    
