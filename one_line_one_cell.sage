from character import *

Parallelism().set('tensor', nproc=4)

def frob_add_one_cell(i,n) :
    diagram = Diagram([(k,0) for k in range(0,n-1) if k!=i]+[(0,1)])
    diagram.draw()
    return E_mu(diagram, parallel=True, r=n-2)

def compare(i,n):
    diagram1 = Diagram([(k,0) for k in range(0,n) if k!=i]+[(0,1)])
    diagram2 = Diagram([(k,0) for k in range(0,n-1)]+[(n-1-i,1)])
    diagram2.draw()
    return E_mu(diagram1, parallel=True, r=n-2) == E_mu(diagram2, parallel=True, r=n-2)

n = 5
for i in range(1,n):
    res = frob_add_one_cell(i,n+1)
    print res
    print compare(i,n)
    print
    print latex_output_character(res)
