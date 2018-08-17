#!/usr/bin/env python
# -*- coding: utf-8 -*-

from sage.combinat.composition import Composition

## Pas encore utilisé : doit être corrigé d'abord


#######################
# Diagrams
#######################

class Diagram() :
    
    """
    A composition ``c = (c_1, c_2, ...)`` is reprensented as a 
    tableau containing ``c_i`` cells in the i_th column. 
    """
    
    def __init__(self,c):
        if not isinstance(c,Composition) :
            c = Composition(c)
        self._c = c
    
    def _repr_(self):
            return "%s"%(self._c)
        
    def _tableau(self) :
        """
        Return the equivalent of the initial tableau for partitions.
        
        EXAMPLES ::
            sage: d = Diagram([1,2])
            sage: d._tableau()
            [[1], [3, 2]]
            sage: d = Diagram([2,1,2,1])
            sage: d._tableau()
            [[2, 1], [3], [5, 4], [6]]

        """
        c = self._c
        res = []
        k = 0
        for i in range(len(c)):
            res += [[c[i]-j1+k for j1 in range(c[i])]]
            k += c[i]
        return res
        
    def size(self) :
        """
        The size of the diagram, which is the number of cells. 
        
        EXAMPLES ::
            sage: d = Diagram([1,2])
            sage: d.size()
            3
            sage: d = Diagram([2,1,2,1])
            sage: d.size()
            6

        """
        return sum(i for i in self._c)
        
    def cells(self) : 
        """
        Gives a list of the coordinates of the cells of the diagram 
        
        EXAMPLES ::
            sage: d = Diagram([1,2])
            sage: d.cells()
            [(0, 0), (1, 0), (1, 1)]
            sage: d = Diagram([2,1,2,1])
            sage: d.cells()
            [(0, 0), (0, 1), (1, 0), (2, 0), (2, 1), (3, 0)]

        """
        c = self._c
        res = []
        for i in range(len(c)) :
            res += [(i,j) for j in range(c[i])]
        return res
