#!/usr/bin/env python
# -*- coding: utf-8 -*-


############################################################
# Diagrams
############################################################

class Diagram() :
    
    # c a composition
    def __init__(self,c):
        if not isinstance(c,Composition) :
            c = Composition(c)
        self._c = c
    
    def _repr_(self):
            return "%s"%(self._c)
        
    def _composition_tableau(self) :
        c = self._c
        res = []
        k = 0
        for i in range(len(c)) : 
            res += [[c[i]-j+k for j in range(c[i])]]
            k += c[i]
        return CompositionTableau(res)
        
    def size(self) :
        return self._composition_tableau().size()
        
    def cells(self) : 
        c = self._c
        res = []
        for i in range(len(c)) :
            res += [(i,j) for j in range(c[i])]
        return res
