from sage.structure.element cimport Element
from sage.groups.perm_gps.permgroup_element cimport PermutationGroupElement

cpdef items_of_vector(Element v)
cpdef act_on_polynomial(p, PermutationGroupElement sigma)
cpdef list diagonal_swap(list exponents, int n, int r, int j1, int j2)
cpdef int diagonal_cmp(list exponents, int n, int r, int j1, int j2)
cpdef reverse_sorting_permutation(t)
def destandardize(self)
def index_filling(t)
