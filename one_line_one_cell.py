%runfile character.py

def frob_add_one_cell(i,n) :
    diagram = Diagram([(k,0) for k in range(0,n-1)]+[(i,1)])
    diagram.draw()
    return E_mu(diagram, parallel=True, r=n-2)

n = 6
res = []
for i in range(0,n-1):
    res += frob_add_one_cell(i,n)
    print(res[i])
    print
    print latex_output_character(res[i])
