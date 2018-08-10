#!/usr/bin/env python
# -*- coding: utf-8 -*-

import inspect
import os
import sage.misc.persist as persist

class func_persist:
    r"""
    Put ``@func_persist`` right before your function
    definition to cache values it computes to disk.

    -- ``key`` - a function that normalizes the input arguments into a unique key
    -- ``hash`` - a function that takes this key and make it into a string (will be used for the name of the file name storing the result) # TODO: file_name? cache_name?
                  TODO: Document that it shall be injective

    """
    def __init__(self, f, dir='func_persist', prefix=None, hash=hash, key=None):
        from sage.misc.misc import sage_makedirs
        self._func = f
        self._dir  = dir
        if prefix is None:
            prefix = f.__name__
        self._prefix = dir+"/"+prefix
        self._hash = hash
        if key is not None:
            self.key = key
        sage_makedirs(dir)
        self.__doc__ = '%s%s%s'%(\
            f.__name__,
            inspect.formatargspec(*inspect.getargs(f.__code__)),
            f.__doc__)

    def key(self, *args, **kwds):
        return (tuple(args), tuple(kwds.items()))

    def __call__(self, *args, **kwds):
        key = self.key(*args, **kwds)
        h = self._hash(key)
        name = '%s_%s.sobj'%(self._prefix, h)

        if os.path.exists(name):
            key2, val = persist.load(name)
            if key == key2:
                # We save and test equality of keys to avoid
                # the (extremely remote) possibility of a hash
                # collision.  Correctness is crucial in mathematics.
                return val

        val = self._func(*args, **kwds)
        persist.save((key, val), name)
        return val

    def dict(self):
        """
        Return the already computed values
        """
        import glob
        return dict(persist.load(name)
                    for name in glob.glob("%s*.sobj"%self._prefix))

