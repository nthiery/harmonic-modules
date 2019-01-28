#!/usr/bin/env python
# -*- coding: utf-8 -*-

from sage.combinat.composition import Composition

## Pas encore utilisé : doit être corrigé d'abord


#######################
# Diagrams
#######################

class Diagram():
    
    """
    A list of cells in the grid $\mathbb{N} \times \mathbb{N}$ : 
    $[(a_1, b_1), (a_2, b_2), ..., (a_n, b_n)]$.
    
    EXAMPLES ::
        sage: d = Diagram([(0,0),(3,0),(6,0)])
        sage: d = Diagram([(0,0),(1,0),(2,0),(3,0),(0,1),(2,1)])

    """
    
    def __init__(self, cells):
        c = True
        for cell in cells:
            if len(cell) != 2:
                c = False
        self._cells = []
        if c:
            for cell in cells:
                self._cells += [(cell[1],cell[0])]
                self._cells.sort()
        else:
            print("Wrong format for class Diagram")

        
    def size(self) :
        """
        The size of the diagram, which is the number of cells. 
        
        EXAMPLES ::
            sage: d = Diagram([(0,0),(3,0),(6,0)])
            sage: d.size()
            3
            
            sage: d = Diagram([(0,0),(1,0),(2,0),(3,0),(0,1),(2,1)])
            sage: d.size()
            6
        """
        return len(self._cells)
        
    def cells(self): 
        """
        Gives the list of the matrix coordinates of the cells of the diagram 
        
        EXAMPLES ::
            sage: d = Diagram([(0,0),(3,0),(6,0)])
            sage: d.cells()
            [(0, 0), (0, 3), (0, 6)]

            sage: d = Diagram([(0,0),(1,0),(2,0),(3,0),(0,1),(2,1)])
            sage: d.cells()
            [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 2)]

        """
        return self._cells
        
    def nb_cols(self):
        """
        Gives the number of columns of the diagram including the empty ones. 
        The number of columns thus corresponds to the greatest $a_i$.

        EXAMPLES ::
            sage: d = Diagram([(0,0),(3,0),(6,0)])
            sage: d.nb_cols()
            7

            sage: d = Diagram([(0,0),(1,0),(2,0),(3,0),(0,1),(2,1)])
            sage: d.nb_cols()
            4

        """
        
        return max([c[1] for c in self.cells()])
