# -*- coding: utf-8 -*-
import datetime
import inspect
import functools
import operator
import os
import sage.misc.persist as persist

from sage.misc.cachefunc import cached_method, cached_function
from sage.misc.misc_c import prod
from sage.misc.constant_function import ConstantFunction

from sage.categories.algebras import Algebras
from sage.categories.cartesian_product import cartesian_product
from sage.categories.tensor import tensor

from sage.parallel.decorate import parallel
from sage.structure.element import have_same_parent
from sage.structure.sage_object import load
from sage.structure.parent import Parent

from sage.structure.unique_representation import UniqueRepresentation

from sage.combinat.integer_lists.invlex import IntegerListsLex
from sage.combinat.partition import Partition, Partitions
from sage.combinat.ranker import rank_from_list
from sage.combinat.sf.sf import SymmetricFunctions
import sage.combinat.tableau
from sage.combinat.words.word import Word
from sage.functions.other import binomial

from sage.groups.perm_gps.permgroup_named import SymmetricGroup
from sage.sets.set import Set

from sage.groups.perm_gps.permgroup_element import PermutationGroupElement
from sage.matrix.constructor import matrix
from sage.modules.free_module_element import vector
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.semirings.non_negative_integer_semiring import NN

from sage.functions.other import factorial

load("code1.pyx")


