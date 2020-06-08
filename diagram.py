#!/usr/bin/env python
# -*- coding: utf-8 -*-

from sage.rings.integer import Integer


class Diagram():
    
    r"""
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
        
        OUTPUT: The number of cells of the diagram.
        
        EXAMPLES:
            sage: d = Diagram([(0,0),(3,0),(6,0)])
            sage: d.size()
            3
            
            sage: d = Diagram([(0,0),(1,0),(2,0),(3,0),(0,1),(2,1)])
            sage: d.size()
            6
        """
        return Integer(len(self._cells))
        
    def cells(self): 
        """
        Gives the list of the matrix coordinates of the cells of the diagram.
        
        OUTPUT: The list of the diagram's cells.
        
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
        Gives the number of columns of the diagram including the empty ones
        that lie between unempty ones. 
        The number of columns thus corresponds to the greatest $a_i$.
        
        OUTPUT: The number of columns of the diagram. 

        EXAMPLES ::
            sage: d = Diagram([(0,0),(3,0),(6,0)])
            sage: d.nb_cols()
            6

            sage: d = Diagram([(0,0),(1,0),(2,0),(3,0),(0,1),(2,1)])
            sage: d.nb_cols()
            3

        """
        
        return max([c[1] for c in self.cells()])
        
    def draw(self):
        """
        Print the diagram. 
        
        EXAMPLES ::
            sage: Diagram([(0,0),(1,1),(2,2)]).draw()
                 _
               _|_|
             _|_| 
            |_|   
            sage: Diagram([(0,0), (1,0), (2,0), (0,1), (2,1)]).draw()
             _   _
            |_|_|_|
            |_|_|_|
            sage: Diagram([(0,2),(1,1),(2,0)]).draw()
             _
            |_|_   
              |_|_ 
                |_|
            sage: Diagram([(0,0),(1,1)]).draw() 
               _
             _|_|
            |_| 
            sage: Diagram([(0,1),(1,0),(1,1)]).draw()  
             _ _
            |_|_|
              |_|
            sage: Diagram([(0,1),(2,2)]).draw()
                 _
             _  |_|
            |_|   
                  
            sage: Diagram([(0,1),(2,3)]).draw()
                 _
                |_|
             _    
            |_|         
            sage: Diagram([(0,1),(3,2),(3,3)]).draw()
                   _
                  |_|
             _    |_|
            |_|     
                    
            sage: Diagram([(0,1),(3,2),(2,3)]).draw()
                 _  
                |_|_ 
             _    |_|
            |_|  
        """
        cells = self.cells()
        max_a = max(a for a,b in cells)
        max_b = max(b for a,b in cells)
        diag_string = []
        k = 0
        for a in range(max_a, -2, -1):
            string = ''
            for b in range(max_b+1):
                if a==-1 and ((0,b) in cells):
                    if (0,b+1) in cells :
                        string += '|_'
                    else:
                        string += '|_|'
                elif a==max_a:
                    if ((a,b) in cells):
                        string += ' _'
                    else:
                        string += '  '
                elif ((a,b) in cells):
                    if b==0 or (a+1,b-1) not in cells:
                        if (a+1,b) in cells:
                            if (a+1, b+1) in cells:
                                string += '|_'
                            else:
                                string += '|_|'
                        else:
                            string += ' _'
                    else:
                        if (a+1,b) in cells:    
                            string += '|_|'
                        elif (a+1,b+1) in cells:
                            string += '_'
                        else :
                            string += '_ '
                else:
                    if b==0 or (a+1,b-1) not in cells:
                        if (a+1,b) in cells:
                            if (a+1, b+1) not in cells:
                                string += '|_|'
                            else:
                                string += '|_'
                        else:
                            string += '  '
                    else:
                        if (a+1,b) in cells:
                            string += '|_|' 
                        else:
                            string += ' '
            print(string)

