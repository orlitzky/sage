r"""
Hypoplactic monoid

This file implements the hypoplactic monoid on the alphabet
`\{1, 2, \ldots, n\}`. Elements are represented by words, with equality
determined by comparing the quasi-ribbon tableaux obtained from
Krob--Thibon insertion. Multiplication is induced by concatenation of
words, followed by replacing the product with its quasi-ribbon reading word
representative.

This file depends on the implementations of quasi-ribbon tableaux.

The main functionality includes constructing hypoplactic monoid elements,
computing their quasi-ribbon insertion tableaux, converting elements to
their quasi-ribbon reading word representatives, multiplying elements, and
computing finite hypoplactic equivalence classes by brute force.

AUTHORS:

- Daniel Chen, Lisa Johnston, Junbok Lee, Evuilynn Nguyen, Heather Ross,
  Anne Schilling, Chenchen Zhao (2026): initial version

REFERENCES:

- [KT1997] Daniel Krob and Jean-Yves Thibon,
  *Noncommutative symmetric functions IV: Quantum linear groups and Hecke
  algebras at q = 0*, Journal of Algebraic Combinatorics 6 (1997),
  no. 4, 339--376.

- [Nov2000] Jean-Christophe Novelli, *On the hypoplactic monoid*,
  Discrete Mathematics 217 (2000), no. 1--3, 315--336.

"""
from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableau, QuasiRibbonTableaux

from sage.structure.parent import Parent
from sage.categories.sets_with_grading import SetsWithGrading
from sage.structure.element_wrapper import ElementWrapper
from sage.structure.unique_representation import UniqueRepresentation
from sage.rings.integer_ring import ZZ
from sage.rings.integer import Integer
from sage.combinat.family import Family

from sage.misc.cachefunc import cached_method
from itertools import permutations

class HypoplacticMonoid(UniqueRepresentation, Parent):
    r"""
    The hypoplactic monoid on the alphabet `\{1, 2, \ldots, n\}`.

    INPUT:

    - ``n`` -- a positive integer; the size of the alphabet

    OUTPUT:

    The hypoplactic monoid of rank ``n``.

    The hypoplactic monoid is a quotient of the free monoid on the alphabet
    `\{1, 2, \ldots, n\}`. In this implementation, elements are represented
    by words in the alphabet `\{1, 2, \ldots, n\}`. Equality is determined by
    comparing the quasi-ribbon tableaux obtained from Krob--Thibon insertion.

    The identity element is the empty word. Multiplication is induced by
    concatenation of words. The product is stored using the quasi-ribbon
    reading word representative obtained from hypoplactic insertion.

    EXAMPLES::

        sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
        sage: H = HypoplacticMonoid(4)
        sage: H
        Hypoplactic monoid of rank 4
        sage: H.rank()
        4

    Elements are constructed from tuples::

        sage: x = H([3, 2, 2, 1])
        sage: x
        3221
        sage: x.to_quasiribbon_tableau()
        [[1], [2, 2], [None, 3]]
        sage: x.to_word()
        word: 2132

    Two words represent the same hypoplactic element when they have the same
    quasi-ribbon insertion tableau::

        sage: H([3, 2, 2, 1]) == H([2, 3, 1, 2])
        True
        sage: H([3, 2, 2, 1]) == H([1, 2, 2, 3])
        False

    Multiplication is induced by concatenation, followed by replacing the
    result with its quasi-ribbon reading word representative::

        sage: H([3]) * H([4])
        34
        sage: H([4]) * H([3])
        43

    TESTS::

        sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
        sage: H = HypoplacticMonoid(4)
        sage: H([]) == H.one()
        True
        sage: len(H.one())
        0
        sage: H.one() * H([3, 2, 2, 1]) == H([3, 2, 2, 1])
        True
        sage: H([3, 2, 2, 1]) * H.one() == H([3, 2, 2, 1])
        True

        sage: HypoplacticMonoid(0)
        Traceback (most recent call last):
        ...
        ValueError: the rank must be a positive integer

        sage: H([1, 2, 5])
        Traceback (most recent call last):
        ...
        ValueError: letters must be integers from 1 to 4

        sage: H([0, 1])
        Traceback (most recent call last):
        ...
        ValueError: letters must be integers from 1 to 4

        sage: H([-1, 2])
        Traceback (most recent call last):
        ...
        ValueError: letters must be integers from 1 to 4

        sage: H([1, 'a'])
        Traceback (most recent call last):
        ...
        ValueError: letters must be integers from 1 to 4

        sage: H([1, 2.5])
        Traceback (most recent call last):
        ...
        ValueError: letters must be integers from 1 to 4
    """

    @staticmethod
    def __classcall_private__(cls, n):
        """
        Normalize the input rank.

        INPUT:

        - ``n`` -- an integer

        OUTPUT:

        The unique hypoplactic monoid of rank ``n``.

        EXAMPLES::

            sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
            sage: HypoplacticMonoid(4) is HypoplacticMonoid(ZZ(4))
            True

        TESTS::

            sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
            sage: HypoplacticMonoid(-1)
            Traceback (most recent call last):
            ...
            ValueError: the rank must be a positive integer
        """
        if not isinstance(n, (int, Integer)):
            raise ValueError("the rank must be a positive integer")
        n = ZZ(n)
        if n <= 0:
            raise ValueError("the rank must be a positive integer")
        return super().__classcall__(cls, n)

    def __init__(self, n):
        """
        Initialize ``self``.

        INPUT:

        - ``n`` -- a positive integer; the size of the alphabet

        EXAMPLES::

            sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
            sage: H = HypoplacticMonoid(4)
            sage: H.rank()
            4
            sage: TestSuite(H).run()
        """
        from sage.categories.monoids import Monoids
        self._n = n
        Parent.__init__(self, category=(Monoids().FinitelyGenerated().Infinite(),
                                        SetsWithGrading().Infinite()))

    def _repr_(self):
        """
        Return a string representation of ``self``.

        EXAMPLES::

            sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
            sage: HypoplacticMonoid(4)
            Hypoplactic monoid of rank 4
        """
        return f"Hypoplactic monoid of rank {self._n}"

    def rank(self):
        """
        Return the rank of ``self``.

        EXAMPLES::

            sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
            sage: HypoplacticMonoid(4).rank()
            4
        """
        return self._n

    @cached_method
    def monoid_generators(self):
        """
        Return the generators of ``self``.

        EXAMPLES::

            sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
            sage: H = HypoplacticMonoid(4)
            sage: G = H.monoid_generators()
            sage: G
            Finite family {1: 1, 2: 2, 3: 3, 4: 4}
            sage: G[1], G[2], G[3], G[4]
            (1, 2, 3, 4)
        """
        from sage.sets.family import Family
        return Family({i: self.element_class(self, (i,))
                       for i in range(1, self._n + 1)})

    @cached_method
    def one(self):
        """
        Return the identity element of ``self``.

        EXAMPLES::

            sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
            sage: H = HypoplacticMonoid(3)
            sage: H.one() == H([])
            True
            sage: len(H.one())
            0
        """
        return self.element_class(self, ())

    @cached_method
    def an_element(self):
        """
        Return an element of ``self``.

        EXAMPLES::

            sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
            sage: H = HypoplacticMonoid(3)
            sage: H.an_element()
            1
        """
        return self.monoid_generators()[1]

    def subset(self, k):
        r"""
        Return the hypoplactic monoid elements represented by words of length ``k``.

        Since the hypoplactic monoid is infinite, this returns the finite set of
        elements of a fixed size, using their canonical reading word representatives.

        EXAMPLES::

            sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
            sage: H = HypoplacticMonoid(2)
            sage: H.subset(1)
            Lazy family (to_word(i))_{i in Quasi-ribbon tableaux of size 1 with entries at most 2}
            sage: list(H.subset(1))
            [1, 2]
            sage: H.subset(2)
            Lazy family (to_word(i))_{i in Quasi-ribbon tableaux of size 2 with entries at most 2}
            sage: list(H.subset(2))
            [21, 11, 12, 22]
        """
        if not isinstance(k, (int, Integer)) or k < 0:
            raise ValueError("the size must be a nonnegative integer")

        quasiribbontableaux = QuasiRibbonTableaux(size=k, max_entry=self.rank())

        def to_word(t):
            return self(t.reading_word())

        return Family(quasiribbontableaux, to_word, lazy=True)

    class Element(ElementWrapper):
        r"""
        An element of a hypoplactic monoid.

        Elements are represented by words in the alphabet
        `\{1, 2, \ldots, n\}`.

        EXAMPLES::
            sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
            sage: H = HypoplacticMonoid(4)
            sage: x = H([3, 2, 2, 1])
            sage: x
            3221
            sage: parent(x)
            Hypoplactic monoid of rank 4
        """
        def __init__(self, parent, value):
            """
            Initialize ``self``.

            INPUT:

            - ``parent`` -- a hypoplactic monoid
            - ``value`` -- a word, given as a list or tuple of letters in the
              alphabet of ``parent``

            TESTS::

                sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
                sage: H = HypoplacticMonoid(4)
                sage: x = H([3, 2, 2, 1]); x
                3221
                sage: H([1, 2.5])
                Traceback (most recent call last):
                ...
                ValueError: letters must be integers from 1 to 4
            """
            r = parent.rank()
            try:
                value = tuple(map(ZZ, value))
            except TypeError:
                raise ValueError("letters must be integers from 1 to %s" % r)
            if not all(1 <= i <= r for i in value):
                raise ValueError("letters must be integers from 1 to %s" % r)
            ElementWrapper.__init__(self, parent, value)

        def _repr_(self):
            """
            Return a string representation of ``self``.

            EXAMPLES::

                sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
                sage: H = HypoplacticMonoid(4)
                sage: H([2, 1, 3])
                213
            """
            if not self.value:
                return ''
            return ''.join(str(x) for x in self.value)

        def __len__(self):
            """
            Return the length of ``self`` as a word.

            This is also the grade of ``self``.

            EXAMPLES::

                sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
                sage: H = HypoplacticMonoid(4)
                sage: len(H([2, 1, 3]))
                3
            """
            return len(self.value)

        grade = __len__

        def to_quasiribbon_tableau(self):
            """
            Return the quasi-ribbon insertion tableau corresponding to ``self``.

            The tableau is computed using Krob--Thibon insertion.

            OUTPUT:

            The quasi-ribbon tableau obtained by inserting the word
            representing ``self``.

            EXAMPLES::

                sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
                sage: H = HypoplacticMonoid(4)
                sage: H([3, 2, 2, 1]).to_quasiribbon_tableau()
                [[1], [2, 2], [None, 3]]
                sage: H([3, 4, 3, 2, 1, 2]).to_quasiribbon_tableau()
                [[1], [2, 2], [None, 3, 3], [None, None, 4]]

            TESTS::
                sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
                sage: H = HypoplacticMonoid(4)
                sage: H([]).to_quasiribbon_tableau()
                []
            """
            Q = QuasiRibbonTableaux()
            return Q.insert_word(self.value)

        def __hash__(self):
            r"""
            Return the hash of ``self``.

            TESTS::

                sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
                sage: H = HypoplacticMonoid(4)
                sage: x = H([2, 3, 1, 2])
                sage: hash(x) == hash(H([2, 3, 1, 2]))
                True
            """
            return hash((self.parent(), self.to_quasiribbon_tableau()))

        def __iter__(self):
            """
            Iterate over the letters of ``self``.

            EXAMPLES::

                sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
                sage: H = HypoplacticMonoid(4)
                sage: list(H([3, 2, 2, 1]))
                [3, 2, 2, 1]
            """
            return iter(self.value)

        def __eq__(self, other):
            r"""
            Return whether ``self`` and ``other`` are equal.

            EXAMPLES::

                sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
                sage: H = HypoplacticMonoid(4)
                sage: H([3, 2, 2, 1]) == H([2, 3, 1, 2])
                True
                sage: H([3, 2, 2, 1]) == H([1, 2, 2, 3])
                False
                sage: H3 = HypoplacticMonoid(3)
                sage: H([2, 1, 3]) == H3([2, 1, 3])
                False
            """
            if self is other:
                return True
            if not hasattr(other, "parent"):
                return False
            if self.parent() != other.parent():
                return False
            return self.to_quasiribbon_tableau() == other.to_quasiribbon_tableau()

        def to_word(self):
            """
            Return the quasi-ribbon reading word representative of ``self``.

            The reading word is obtained from the quasi-ribbon insertion
            tableau by reading columns from left to right, and from bottom to
            top within each column.

            OUTPUT:

            A tuple containing the quasi-ribbon reading word of ``self``.

            EXAMPLES::

                sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
                sage: H = HypoplacticMonoid(4)
                sage: H([3, 2, 2, 1]).to_word()
                word: 2132
                sage: H([3, 4, 3, 2, 1, 2]).to_word()
                word: 213243

            TESTS::

                sage: H = HypoplacticMonoid(4)
                sage: H([]).to_word()
                word:
            """
            return self.to_quasiribbon_tableau().reading_word()

        def _mul_(self, other):
            """
            Multiply ``self`` by ``other``.

            Multiplication is induced by concatenation of words. The
            concatenated word is inserted using hypoplactic insertion, and the
            product is stored using the resulting quasi-ribbon reading word
            representative.

            INPUT:

            - ``other`` -- an element of the hypoplactic monoid

            OUTPUT:

            The product of ``self`` and ``other``.

            EXAMPLES::

                sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
                sage: H = HypoplacticMonoid(4)
                sage: a = H([3])
                sage: b = H([4])
                sage: a * b
                34

                sage: c = H([4])
                sage: d = H([3])
                sage: c * d
                43

            TESTS::

                sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
                sage: H = HypoplacticMonoid(4)
                sage: H([]) * H([3, 2, 2, 1]) == H([3, 2, 2, 1])
                True
                sage: H([3, 2, 2, 1]) * H([]) == H([3, 2, 2, 1])
                True
            """
            parent = self.parent()
            word = self.value + other.value
            product_word = self.__class__(parent, word)
            T = product_word.to_quasiribbon_tableau()
            canonical_word = T.reading_word()
            return self.__class__(parent, canonical_word)

        def is_canonical(self):
            """
            Return whether ``self`` is its row reading word representative.

            EXAMPLES::

                sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
                sage: H = HypoplacticMonoid(4)
                sage: H([3, 2, 2, 1]).is_canonical()
                False
                sage: H([2,1,3,2]).is_canonical()
                True
            """
            return list(self.value) == list(self.to_word())

        def equivalence_class(self):
            r"""
            Return the hypoplactic equivalence class of ``self``.

            This is the list of all words with the same quasiribbon insertion tableau
            as ``self``.

            Because this method relies on brute-force checking, it is suitable mostly for
            short words in parent classes on small alphabets.

            EXAMPLES::

                sage: from sage.monoids.hypoplactic_monoid import HypoplacticMonoid
                sage: H = HypoplacticMonoid(3)
                sage: H([2, 1, 3]).equivalence_class()
                [213, 231]

                sage: H = HypoplacticMonoid(4)
                sage: H([3, 1, 4, 2]).equivalence_class()
                [1324, 1342, 3124, 3142, 3412]
            """
            parent = self.parent()
            # Any equivalent word must have the same letters as ``self``, so we
            # only need to check rearrangements of the current word. The ``set``
            # removes duplicates when letters repeat.
            words = sorted(set(permutations(self.value)))
            # Keep exactly the rearrangements whose quasiribbon insertion tableau agrees
            # with the original one.
            return [parent(w) for w in words if parent(w).to_quasiribbon_tableau() == self.to_quasiribbon_tableau()]
