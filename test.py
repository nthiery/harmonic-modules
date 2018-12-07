def symmetrize(p, n):
    """
    Symmetrize the polynomial p in n variables
    """
    
    p_sym = p
    for sigma in Permutations(n):
        result = act_on_polynomial(p, PermutationGroupElement(sigma))
        for t in result:
            if t not in p:
                p_sym += t[1]
    return p_sym
