# -*- coding: utf-8 -*-

# Ideally, we would put this in an ".ipy" file to be able to use magic
# commands, but this causes trouble with the unicode character below

# %run "code.py"
# %display unicode_art

tensor.symbol=u" ⊗ "
Partitions.options.convention = "french"
Partitions.options.display = "list"
from sage.typeset.unicode_art import UnicodeArt
Partition._unicode_art_ = lambda p: UnicodeArt([''.join(str(i) for i in p)])
SymmetricFunctions(QQ).inject_shorthands(verbose=False)
