r"""
Graph genus algorithms

This module integrates algorithms for the orientable genus of a simple
connected graph.  The built-in ``'simple'`` algorithm is always available.
The optional :ref:`graph_genus <spkg_graph_genus>` package provides the
``'page'`` and ``'multi_genus'`` algorithms.

AUTHORS:

- Tom Boothby (2010): original simple backtracking algorithm
- Alexander Metzger and Austin Ulrigg (2026): PAGE algorithm
- Gunnar Brinkmann (2022): MultiGenus algorithm
- Alexander Metzger (2026): Sage integration of PAGE and MultiGenus
"""

# ****************************************************************************
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from sage.graphs.genus_simple import simple_connected_genus_backtracker
from sage.graphs.genus_simple import simple_connected_graph_genus as simple_graph_genus


def _graph_genus():
    r"""
    Return the optional :mod:`graph_genus` module, or raise a feature error.
    """
    try:
        import graph_genus
    except ImportError:
        from sage.features.graph_genus import GraphGenus

        GraphGenus().require()
    return graph_genus


def _has_graph_genus():
    r"""
    Return whether the optional :mod:`graph_genus` module is importable.
    """
    try:
        import graph_genus  # noqa: F401
    except ImportError:
        return False
    return True


def _select_algorithm(algorithm):
    r"""
    Normalize the genus algorithm selection.
    """
    if algorithm is None:
        if _has_graph_genus():
            return 'page'
        return 'simple'
    if algorithm not in ('page', 'multi_genus', 'simple'):
        raise ValueError("unknown algorithm {!r}".format(algorithm))
    return algorithm


def simple_connected_graph_genus(
    G, set_embedding=False, check=True, minimal=True, algorithm=None
):
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

    - ``algorithm`` -- string or ``None`` (default: ``None``); one of
      ``'page'``, ``'multi_genus'``, or ``'simple'``.  If ``None``, Sage uses
      ``'page'`` when the optional :ref:`graph_genus <spkg_graph_genus>`
      package is installed and otherwise uses ``'simple'``.

    OUTPUT: integer; the orientable genus of ``G``

    EXAMPLES::

        sage: import sage.graphs.genus
        sage: from sage.graphs.genus import simple_connected_graph_genus as genus
        sage: graphs.CompleteGraph(5).genus()
        1
        sage: graphs.CompleteGraph(5).genus(algorithm='simple')
        1
        sage: graphs.CompleteGraph(5).genus(algorithm='page')      # optional - graph_genus
        1
        sage: graphs.CompleteGraph(5).genus(algorithm='multi_genus')  # optional - graph_genus
        1
        sage: G = graphs.PetersenGraph()
        sage: genus(G, algorithm='simple')
        1
        sage: genus(G, algorithm='page')                            # optional - graph_genus
        1
        sage: genus(G, algorithm='multi_genus')                     # optional - graph_genus
        1

    ALGORITHM:

    The ``'simple'`` algorithm is always available and is the fallback default
    when the optional :ref:`graph_genus <spkg_graph_genus>` package is not
    installed.  It is a direct rotation-system enumeration; it is useful for
    maximum genus and as a compact reference implementation, but has much worse
    scaling.

    The optional ``'page'`` algorithm is provided by ``graph_genus`` and is
    based on the cycle-fitting method of [MetUlr2026]_.  It is usually the best
    choice for low-degree sparse graphs. For example, PAGE solves 3-cages
    through many girth-9 examples in seconds where the simple enumerator takes
    days or does not finish.  The optional ``'multi_genus'`` algorithm is also
    provided by ``graph_genus`` and wraps Brinkmann's implementation [Bri2022]_,
    which is often extremely fast on complete, complete multipartite, and many
    dense/small examples, but has fixed C integer-size limits.

    TESTS::

        sage: G = graphs.CompleteGraph(5)
        sage: assert genus(G, set_embedding=True, algorithm='simple') == 1
        sage: assert len(G.faces(G.get_embedding())) == 5
        sage: for alg in ('page', 'multi_genus'):                 # optional - graph_genus
        ....:     G = graphs.CompleteGraph(5)
        ....:     assert genus(G, set_embedding=True, algorithm=alg) == 1
        ....:     assert len(G.faces(G.get_embedding())) == 5
        sage: genus(graphs.CompleteGraph(5), set_embedding=False,  # optional - graph_genus
        ....:       algorithm='multi_genus')
        1
        sage: genus(graphs.CompleteGraph(5), algorithm='unknown')
        Traceback (most recent call last):
        ...
        ValueError: unknown algorithm 'unknown'
        sage: genus(graphs.CompleteGraph(5), minimal=False,        # optional - graph_genus
        ....:       algorithm='page')
        Traceback (most recent call last):
        ...
        NotImplementedError: algorithm 'page' only computes minimum genus
    """
    algorithm = _select_algorithm(algorithm)

    if algorithm != 'simple' and not minimal:
        raise NotImplementedError(
            "algorithm {!r} only computes minimum genus".format(algorithm)
        )

    if minimal and G.is_planar(set_embedding=set_embedding):
        return 0

    if check:
        if not G.is_connected():
            raise ValueError("cannot compute the genus of a disconnected graph")
        if G.is_directed() or G.has_multiple_edges() or G.has_loops():
            G = G.to_simple()

    if algorithm == 'simple':
        return simple_graph_genus(
            G, set_embedding=set_embedding, check=False, minimal=minimal
        )
    return _graph_genus_algorithm(G, set_embedding, algorithm)


def _graph_genus_algorithm(G, set_embedding, algorithm):
    r"""
    Compute genus using the optional :mod:`graph_genus` package.
    """
    graph_genus = _graph_genus()
    vertices = list(G)
    index = {v: i for i, v in enumerate(vertices)}
    adjacency_list = []

    for v in vertices:
        row = [index[u] for u in G.neighbor_iterator(v)]
        row.sort()
        adjacency_list.append(row)

    genus, rotation = graph_genus.embed(adjacency_list, algorithm=algorithm)

    if set_embedding:
        embedding = {}
        for i, v in enumerate(vertices):
            embedding[v] = [vertices[j] for j in rotation[i]]
        G.set_embedding(embedding)

    return genus
