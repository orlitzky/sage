"""
Graph genus algorithms.

This module integrates three algorithms for the orientable genus of a graph:

- ``'page'`` -- the default.  This is the PAGE cycle-fitting algorithm
  [MetUlr2026]_.  It is often orders of magnitude faster than direct 
  rotation-system enumeration especially on low-degree, high girth, 
  and sparse graphs.

- ``'multi_genus'`` -- Brinkmann's edge-insertion implementation [Bri2022]_.
  It is very fast on many dense, complete, complete multipartite, and small
  miscellaneous graphs.

- ``'simple'`` -- a simple backtracking algorithm.  It enumerates local
  rotation systems directly.  It supports maximum genus, but generally scales as
  a product of local rotation permutations and is the slowest option on larger
  nonplanar graphs.
"""

# ****************************************************************************
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from libc.stdlib cimport free, malloc

from sage.graphs.genus_simple import simple_connected_genus_backtracker
from sage.graphs.genus_simple import simple_connected_graph_genus as simple_graph_genus

cdef extern from "genus_page.h":
    int sage_page_genus(int n, int m, int degree, const int *degrees,
                        const int *neighbors, int stride, int *rotation,
                        int rotation_stride, int *genus_out)

cdef extern from "genus_multigenus.h":
    int sage_multigenus_genus(int n, int m, const int *degrees,
                              const int *neighbors, int stride, int *rotation,
                              int rotation_stride, int *genus_out)


def simple_connected_graph_genus(G, set_embedding=False, check=True, minimal=True, algorithm="page"):
    r"""
    Compute the genus of a simple connected graph.

    INPUT:

    - ``G`` -- a simple connected graph

    - ``set_embedding`` -- boolean (default: ``False``); whether to store a
      minimum-genus combinatorial embedding on ``G``

    - ``check`` -- boolean (default: ``True``); whether to validate and simplify
      the graph before the computation

    - ``minimal`` -- boolean (default: ``True``); whether to compute minimum
      genus.  If ``False``, only ``algorithm='simple'`` is supported.

    - ``algorithm`` -- string (default: ``'page'``); one of ``'page'``,
      ``'multi_genus'``, or ``'simple'``

    OUTPUT: integer; the orientable genus of ``G``

    EXAMPLES::

        sage: import sage.graphs.genus
        sage: from sage.graphs.genus import simple_connected_graph_genus as genus
        sage: graphs.CompleteGraph(5).genus()
        1
        sage: graphs.CompleteGraph(5).genus(algorithm='simple')
        1
        sage: graphs.CompleteGraph(5).genus(algorithm='multi_genus')
        1
        sage: G = graphs.PetersenGraph()
        sage: genus(G, algorithm='simple')
        1
        sage: genus(G, algorithm='multi_genus')
        1

    ALGORITHM:

    The ``'page'`` algorithm is based on the cycle-fitting method of
    [MetUlr2026]_.  It is usually the best default especially for low-degree sparse
    graphs. For example, PAGE solves 3-cages through many girth-9 examples in seconds 
    where the simple enumerator takes days or does not finish.
    The ``'multi_genus'`` algorithm wraps Brinkmann's implementation [Bri2022]_, 
    which is often extremely fast on complete, complete multipartite, and many 
    dense/small examples, but has fixed C integer-size limits.  
    The ``'simple'`` algorithm is a direct rotation-system enumeration; 
    it is useful for maximum genus and as a compact reference implementation, 
    but has much worse scaling.
    """
    if algorithm not in ('page', 'multi_genus', 'simple'):
        raise ValueError("unknown algorithm {!r}".format(algorithm))

    if algorithm != 'simple' and not minimal:
        raise NotImplementedError("algorithm {!r} only computes minimum genus".format(algorithm))

    if minimal and G.is_planar(set_embedding=set_embedding):
        return 0

    if check:
        if not G.is_connected():
            raise ValueError("cannot compute the genus of a disconnected graph")
        if G.is_directed() or G.has_multiple_edges() or G.has_loops():
            G = G.to_simple()

    if algorithm == 'simple':
        return simple_graph_genus(G, set_embedding=set_embedding, check=False,
                                  minimal=minimal)
    if algorithm == 'page':
        return _c_algorithm_graph_genus(G, set_embedding, True)
    return _c_algorithm_graph_genus(G, set_embedding, False)


cdef int _c_algorithm_graph_genus(G, bint set_embedding, bint use_page) except -99:
    cdef int n = G.order()
    cdef int m = G.size()
    cdef int stride = 0
    cdef int i, j, result, genus
    cdef int *degrees = NULL
    cdef int *neighbors = NULL
    cdef int *rotation = NULL
    vertices = list(G)
    index = {v: i for i, v in enumerate(vertices)}

    if n <= 1:
        if set_embedding:
            G.set_embedding({v: [] for v in vertices})
        return 0

    for v in vertices:
        stride = max(stride, len(list(G.neighbor_iterator(v))))
    if stride == 0:
        if set_embedding:
            G.set_embedding({v: [] for v in vertices})
        return 0

    degrees = <int *>malloc(n * sizeof(int))
    neighbors = <int *>malloc(n * stride * sizeof(int))
    if set_embedding:
        rotation = <int *>malloc(n * stride * sizeof(int))
    if degrees == NULL or neighbors == NULL or (set_embedding and rotation == NULL):
        free(degrees)
        free(neighbors)
        free(rotation)
        raise MemoryError

    try:
        for i in range(n * stride):
            neighbors[i] = 0
            if rotation != NULL:
                rotation[i] = -1
        for i, v in enumerate(vertices):
            row = [index[u] for u in G.neighbor_iterator(v)]
            row.sort()
            degrees[i] = len(row)
            for j, u in enumerate(row):
                neighbors[i * stride + j] = u

        if use_page:
            result = sage_page_genus(n, m, stride, degrees, neighbors, stride,
                                     rotation, stride, &genus)
        else:
            result = sage_multigenus_genus(n, m, degrees, neighbors, stride,
                                           rotation, stride, &genus)
        if result < 0:
            if use_page:
                raise RuntimeError("PAGE failed with status {}".format(result))
            if result == -2:
                raise ValueError("graph is too large for the MultiGenus integer type")
            raise RuntimeError("MultiGenus failed with status {}".format(result))

        if set_embedding:
            embedding = {}
            for i, v in enumerate(vertices):
                embedding[v] = [vertices[rotation[i * stride + j]]
                                for j in range(degrees[i])]
            G.set_embedding(embedding)
    finally:
        free(degrees)
        free(neighbors)
        free(rotation)

    return genus
