r"""
Quasi-ribbon tableaux

AUTHORS:

- Daniel Chen, Lisa Johnston, Junbok Lee, Evuilynn Nguyen, Heather Ross, Anne Schilling, Chenchen Zhao (2026): initial version

This file implements quasi-ribbon tableaux and finite families of
quasi-ribbon tableaux. A quasi-ribbon tableau is entered as a list of rows
from top to bottom. The entries in each row are weakly increasing left to right, the
entries in each column are strictly increasing top to bottom, and ``None`` entries are used
to record the shifted positions in the ribbon shape.

This file consists of the following major classes:

Element classes:

* :class:`QuasiRibbonTableau`

Parent classes:

* :class:`QuasiRibbonTableaux`

The main functionality includes constructing quasi-ribbon tableaux,
computing their associated compositions, computing column-reading words,
generating finite families of fixed composition shape, and performing
Krob--Thibon insertion of letters and words.

REFERENCES:

- [KT1997] Daniel Krob and Jean-Yves Thibon,
  *Noncommutative symmetric functions IV: Quantum linear groups and Hecke
  algebras at q = 0*, Journal of Algebraic Combinatorics 6 (1997),
  no. 4, 339--376.

- [Nov2000] Jean-Christophe Novelli, *On the hypoplactic monoid*, Discrete Mathematics 217 (2000), no. 1--3, 315--336.


"""
from sage.categories.sets_cat import Sets
from sage.combinat.skew_tableau import SkewTableau, SkewTableaux
from sage.combinat.composition import Composition, Compositions
from sage.rings.integer import Integer
from sage.sets.positive_integers import PositiveIntegers
from sage.combinat.words.words import Words
from sage.rings.integer_ring import ZZ
from sage.rings.infinity import infinity

class QuasiRibbonTableau(SkewTableau):
    r"""
    A quasi-ribbon tableau.

    A quasi-ribbon shape is obtained
    from a composition by drawing rows of cells whose lengths are the parts of
    the composition, and then shifting the rows so that each lower row starts
    under the last cell of the row above. For the purposes of this class, a quasi-ribbon
    tableau is a filling of a quasi-ribbon shape with positive integers which:

    1) has at least one entry in row `1`;
    2) weakly increases from left to right in each row; and
    3) strictly increases from top to bottom in each column.

    A quasi-ribbon tableau is given by a list of the rows from top to bottom.

    EXAMPLES::

        sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableau
        sage: Q = QuasiRibbonTableau([[1, 2, 3],
        ....:                         [None, None, 4, 5]])
        sage: Q
        [[1, 2, 3], [None, None, 4, 5]]
        sage: Q.pp()
        .  .  4  5
        1  2  3
        sage: print(Q)
        1  2  3
              4  5
        sage: Q.to_composition()
        [3, 2]

    The entries labeled by ``None`` correspond to shifted positions before the
    first actual entry in a row.  Using ``None`` is optional;
    the entries will be shifted accordingly::

        sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableau
        sage: Q = QuasiRibbonTableau([[1, 2, 3], [4, 5]])
        sage: print(Q)
        1  2  3
              4  5

    TESTS::

        sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableau
        sage: Q = QuasiRibbonTableau([[1], [2, 3], [4, 4]])
        sage: Q.to_word()
        word: 12344
        sage: QuasiRibbonTableau([[1,2],[3,4]]).evaluation()
        [1, 1, 1, 1]
        sage: TestSuite(Q).run()
    """
    @staticmethod
    def __classcall_private__(cls, rows):
        r"""
        Normalize input and return a quasi-ribbon tableau object.

        We use it to check that the input is made of rows and that entries
        are positive integers or ``None``.

        The user may either include the ``None`` entries manually or enter
        rows without ``None`` entries. In both cases, we remove all
        user-given ``None`` entries first and then rebuild the shifted shape
        using our quasi-ribbon convention.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableau
            sage: QuasiRibbonTableau([[1, 2], [None, 3]])
            [[1, 2], [None, 3]]
            sage: QuasiRibbonTableau([[1, 2, 3], [4, 5]])
            [[1, 2, 3], [None, None, 4, 5]]
            sage: QuasiRibbonTableau([[1, 2, 3], [None, 4, 5]])
            [[1, 2, 3], [None, None, 4, 5]]
            sage: QuasiRibbonTableau([[1, 2, 3], [4, 5], [6]])
            [[1, 2, 3], [None, None, 4, 5], [None, None, None, 6]]

        TESTS::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableau
            sage: QuasiRibbonTableau([1, 2])
            Traceback (most recent call last):
            ...
            TypeError: rows must be lists of positive integers
            sage: QuasiRibbonTableau([[1, -2]])
            Traceback (most recent call last):
            ...
            TypeError: entries must be positive integers or None
            sage: QuasiRibbonTableau([[None]])
            Traceback (most recent call last):
            ...
            TypeError: a skew tableau cannot have an empty list for a row
        """
        try:
            r = [tuple(row) for row in rows]
        except TypeError:
            raise TypeError("rows must be lists of positive integers")
        if not all(entry is None or (isinstance(entry, (int, Integer)) and entry > 0)
                   for row in r for entry in row):
            raise TypeError("entries must be positive integers or None")
        clean_rows = [tuple(entry for entry in row if entry is not None) for row in r]
        return QuasiRibbonTableaux()(clean_rows)

    def __init__(self, parent, rows):
        """
        Initialize ``self``.

        The input rows are in quasi-ribbon orientation, from top to bottom.
        We store these rows for our own quasi-ribbon methods, but we also flip
        them before calling ``SkewTableau.__init__`` so that the object uses
        Sage's skew tableau infrastructure.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableau
            sage: Q = QuasiRibbonTableau([[1, 2, 3],
            ....:                         [None, None, 4, 5]])
            sage: Q.rows()
            [[1, 2, 3], [None, None, 4, 5]]
        """
        for row in rows:
            for i in range(len(row) - 1):
                if row[i] > row[i + 1]:
                    raise ValueError("rows must be weakly increasing")
        shifted_rows = []
        shift = 0
        for row in rows:
            shifted_rows.append(list([None] * shift + list(row)))
            shift += len(row) - 1
        width = len(shifted_rows[-1]) if shifted_rows else 0
        for col_num in range(width):
            col = []
            for row in shifted_rows:
                if col_num < len(row) and row[col_num] is not None:
                    col.append(row[col_num])
            for i in range(len(col) - 1):
                if col[i] >= col[i + 1]:
                    raise ValueError("columns must be strictly increasing")
        SkewTableau.__init__(self, parent, shifted_rows[::-1])

    def rows(self):
        """
        Return the quasi-ribbon rows of ``self``.

        This returns the user-facing row-list representation, including
        ``None`` entries.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableau
            sage: Q = QuasiRibbonTableau([[1, 2, 3],
            ....:                         [None, None, 4, 5]])
            sage: Q.rows()
            [[1, 2, 3], [None, None, 4, 5]]
        """
        return [list(row) for row in self[::-1]]

    def to_composition(self):
        """
        Return the composition shape of ``self``.

        The shape counts the actual entries in each row, ignoring ``None``.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableau
            sage: Q = QuasiRibbonTableau([[1, 2, 3],
            ....:                         [None, None, 4, 5]])
            sage: Q.to_composition()
            [3, 2]
        """
        # Each row length in the composition is the number of non-None entries
        # in that row.
        return Composition(
            [sum(entry is not None for entry in row) for row in self.rows()])

    def width(self):
        """
        Return the maximum row length of ``self``, including ``None`` entries.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableau
            sage: Q = QuasiRibbonTableau([[1, 2, 3],
            ....:                         [None, None, 4, 5]])
            sage: Q.width()
            4
        """
        # The empty tableau has width 0.
        if not self.rows():
            return 0

        # We include None entries because they represent shifted positions.
        return max(len(row) for row in self.rows())

    def __hash__(self):
        r"""
        Return the hash of ``self``.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableau
            sage: Q = QuasiRibbonTableau([[1, 2], [3]])
            sage: hash(tuple(Q)) == hash(Q)
            True
        """
        return hash(tuple(self))

    def to_word_by_column(self):
        """
        Return the reading word of ``self``.

        The reading convention is column by column from left to right.
        Within each column, read from bottom to top.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableau
            sage: Q = QuasiRibbonTableau([[1, 2, 3],
            ....:                         [None, None, 4, 5]])
            sage: Q.to_word_by_column()
            word: 12435

            sage: T = QuasiRibbonTableau([[1], [2, 2], [None, 3, 3], [None, None, 4]])
            sage: T.to_word_by_column()
            word: 213243
        """
        rows = self.rows()
        word = []

        for col in range(self.width()):
            for row in rows[::-1]:
                if col < len(row) and row[col] is not None:
                    word.append(row[col])

        return Words(PositiveIntegers())(word)

    def _repr_(self):
        """
        Return a string representation of ``self``.

        This displays the user-facing quasiribbon rows, not the internally
        flipped skew-tableau rows.

        EXAMPLES::

            sage: Q = QuasiRibbonTableau([[1,2,2],[3]])
            sage: Q
            [[1, 2, 2], [None, None, 3]]
        """
        # Keep the raw row-list output for debugging because it shows None
        # entries explicitly.
        return repr(self.rows())

    def __str__(self):
        """
        Return a readable string version of ``self``.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableau
            sage: Q = QuasiRibbonTableau([[1, 2, 3],
            ....:                         [None, None, 4, 5]])
            sage: print(Q)
            1  2  3
                  4  5
        """
        lines = []
        for row in self.rows():
            # Print None entries as blank spaces rather than the word "None".
            line = "  ".join(" " if entry is None else str(entry) for entry in row)
            lines.append(line)
        return "\n".join(lines)

    def _clean_rows(self):
        """
        Return the rows of ``self`` with the ``None`` entries removed.

        The tableau stores shifted positions using ``None`` entries, but for
        insertion it is often easier to work only with the actual entries.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableau
            sage: Q = QuasiRibbonTableau([[1, 2, 3], [4, 5]])
            sage: Q.rows()
            [[1, 2, 3], [None, None, 4, 5]]
            sage: Q._clean_rows()
            [[1, 2, 3], [4, 5]]
        """
        return [[entry for entry in row if entry is not None] for row in self.rows()]

    def _entries_with_positions(self):
        """
        Return all entries of ``self`` with their positions in the cleaned rows.

        Each item is a tuple (entry, row_index, col_index).

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableau
            sage: Q = QuasiRibbonTableau([[1, 2, 3], [4, 5]])
            sage: Q._entries_with_positions()
            [(1, 0, 0), (2, 0, 1), (3, 0, 2), (4, 1, 0), (5, 1, 1)]
        """
        entries = []
        for row_index, row in enumerate(self._clean_rows()):
            for col_index, entry in enumerate(row):
                if entry is not None:
                    entries.append((entry, row_index, col_index))
        return entries

    def _rightmost_bottommost_leq(self, a):
        """
        Find the rightmost, bottommost entry of ``self`` that is less or equal to ``a``.

        Returns (entry, row_index, col_index), or ``None`` if no entry is less or equal to `a`.

        We compare positions by column first, then row. So "rightmost" means
        largest column index. If there is a tie, "bottommost" means largest
        row index.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableau
            sage: Q = QuasiRibbonTableau([[1, 2, 3], [4, 5]])
            sage: Q._rightmost_bottommost_leq(3)
            (3, 0, 2)
            sage: Q = QuasiRibbonTableau([[1, 2, 2], [3, 3]])
            sage: Q._rightmost_bottommost_leq(3)
            (3, 1, 1)
        """
        candidates = []
        for entry, row_index, col_index in self._entries_with_positions():
            if entry <= a:
                candidates.append((entry, row_index, col_index))
        if not candidates:
            return None
        # Pick the candidate with largest row index, then largest column index.
        return max(candidates, key=lambda item: (item[1], item[2]))

    def split(self, row_index, col_index):
        """
        Return two quasi-ribbon tableaux split from ``self``.

        The first quasi-ribbon tableau includes
        all entries above or weakly left of the (``row_index``, ``col_index``)-position
        and the second includes all entries below or strictly right of that
        position. ``col_index`` indicates the position among integers in a row, ignoring
        the ``None`` entries; both it and ``row_index`` count starting from 0.

        When ``row_index`` exceeds the number of rows, the first quasi-ribbon
        tableau is ``self`` and the second is empty. When ``column_index`` exceeds the
        number of integers in ``self.rows()[row_index]``, the first quasi-ribbon
        contains the entirety of ``self.rows()[row_index]`` and the second starts
        at the row below.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableau
            sage: Q = QuasiRibbonTableau([[1, 2, 3], [4, 5]])
            sage: Q1, Q2 = Q.split(0, 0)
            sage: Q1.rows()
            [[1]]
            sage: Q2.rows()
            [[2, 3], [None, 4, 5]]
            sage: Q3, Q4 = Q.split(1, 0)
            sage: Q3.rows()
            [[1, 2, 3], [None, None, 4]]
            sage: Q4.rows()
            [[5]]
        """
        rows = self._clean_rows()
        ## Edge case: rows has fewer rows than row_index
        if len(rows) <= row_index:
            return self, QuasiRibbonTableau([])
        top_rows = rows[:row_index] + [rows[row_index][:col_index+1]]
        ## Prepare for edge case: column_index exceeds the number
        ## of integers in the desired row
        tail = [rows[row_index][col_index+1:]]
        if tail[0]:
            bottom_rows = tail + rows[row_index+1:]
        else:
            bottom_rows = rows[row_index+1:]
        return QuasiRibbonTableau(top_rows), QuasiRibbonTableau(bottom_rows)

    def insert_letter(self, a):
        """
        Insert one letter a into a quasi-ribbon tableau ``self``.

        Case 1:
        If no entry of ``self`` is less or equal to ``a``, add a as a new top row.

        Case 2:
        Otherwise, find `x`, the rightmost and bottommost entry of ``self`` that is less or equal to `a`.
        Put a immediately to the right of `x`. Then split off the entries that
        were originally to the right of `x` and move them below.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableau
            sage: Q = QuasiRibbonTableau([])
            sage: Q.insert_letter(3)
            [[3]]

            sage: Q = QuasiRibbonTableau([[4, 5]])
            sage: Q.insert_letter(3)
            [[3], [4, 5]]

            sage: Q = QuasiRibbonTableau([[1, 2, 3], [4, 5]])
            sage: Q.insert_letter(4)
            [[1, 2, 3], [None, None, 4, 4], [None, None, None, 5]]
        """
        if not isinstance(a, (int, Integer)) or a <= 0:
            raise ValueError("the inserted letter must be a positive integer")

        rows = self._clean_rows()

        # Empty tableau case.
        if not rows:
            return QuasiRibbonTableau([[a]])

        site = self._rightmost_bottommost_leq(a)

        # Case 1: there is no entry <= a.
        # Put a in a new top row and place the old tableau below it.
        if site is None:
            new_rows = [[a]] + rows
            return QuasiRibbonTableau(new_rows)

        # Case 2: Standard case.
        _, row_index, col_index = site
        Q1, Q2 = self.split(row_index, col_index)
        Q1_bumped = Q1.rows()[:row_index] + [Q1.rows()[row_index] + [a]]
        return QuasiRibbonTableau(Q1_bumped + Q2.rows())

    def insert_word(self, word):
        """
        Insert the letters of a ``word`` one at a time from left to right into ``self``.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableau
            sage: Q = QuasiRibbonTableau([])
            sage: Q.insert_word([3])
            [[3]]

            sage: Q = QuasiRibbonTableau([[4, 5]])
            sage: Q.insert_word([3,3,1,2])
            [[1, 2], [None, 3, 3], [None, None, 4, 5]]

            sage: Q = QuasiRibbonTableau([[1], [2,3]])
            sage: Q.insert_word([])
            [[1], [2, 3]]
            sage: Q.insert_word([4,1,2])
            [[1, 1], [None, 2, 2], [None, None, 3, 4]]
        """
        Q = QuasiRibbonTableau(self.rows())
        for a in word:
            if not isinstance(a, (int, Integer)) or a <= 0:
                raise ValueError("the inserted letters must be positive integers")
            Q = Q.insert_letter(a)
        return Q

    def _test_quasi_ribbon(self, **options):
        r"""
        Test that ``self`` satisfies the quasi-ribbon conditions.
        """
        tester = self._tester(**options)
        rows = self.rows()

        expected_shift = 0
        for row in rows:
            shift = 0
            while shift < len(row) and row[shift] is None:
                shift += 1

            entries = row[shift:]

            tester.assertTrue(entries)
            tester.assertTrue(all(entry is not None for entry in entries))
            tester.assertEqual(shift, expected_shift)
            tester.assertTrue(
                all(entries[i] <= entries[i + 1]
                    for i in range(len(entries) - 1))
            )

            expected_shift += len(entries) - 1

        width = max((len(row) for row in rows), default=0)
        for col in range(width):
            entries = [
                row[col]
                for row in rows
                if col < len(row) and row[col] is not None
            ]
            tester.assertTrue(
                all(entries[i] < entries[i + 1]
                    for i in range(len(entries) - 1))
            )

class QuasiRibbonTableaux(SkewTableaux):
    r"""
    The set of quasi-ribbon tableaux.

    INPUT:

    - ``shape`` -- (optional) the composition shape of the rows
    - ``max_entry`` -- (optional) the largest allowed entry for finite generation

    EXAMPLES::

        sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableaux
        sage: QRT = QuasiRibbonTableaux()
        sage: QRT
        Quasi-ribbon tableaux
        sage: QRT = QuasiRibbonTableaux(shape=[2, 1])
        sage: QRT
        Quasi-ribbon tableaux of shape [2, 1]
        sage: QRT = QuasiRibbonTableaux(shape=[2, 1], max_entry=3)
        sage: QRT.list()
        [[[1, 1], [None, 2]],
        [[1, 1], [None, 3]],
        [[1, 2], [None, 3]],
        [[2, 2], [None, 3]]]
        """

    @staticmethod
    def __classcall_private__(cls, shape=None, max_entry=None, size=None, category=None):
        """
        Normalize input before constructing the parent object.

        TESTS::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableaux
            sage: QRT = QuasiRibbonTableaux()
            sage: QRT
            Quasi-ribbon tableaux
            sage: QRT = QuasiRibbonTableaux(shape=[2, 1])
            sage: QRT
            Quasi-ribbon tableaux of shape [2, 1]
            sage: QuasiRibbonTableaux((3, 1))
            Quasi-ribbon tableaux of shape [3, 1]
            sage: QuasiRibbonTableaux(4)
            Quasi-ribbon tableaux of size 4
            sage: QRT = QuasiRibbonTableaux(shape=[2, 1], max_entry=3)
            sage: QRT
            Quasi-ribbon tableaux of shape [2, 1] with entries at most 3
            sage: QuasiRibbonTableaux(4, max_entry=3)
            Quasi-ribbon tableaux of size 4 with entries at most 3
            sage: TestSuite(QRT).run()
        """
        if shape is not None and size is None:
            if shape in ZZ:
                size = Integer(shape)
                shape = None
            else:
                shape = tuple(shape)
        # Do not allow both shape and size
        if shape is not None and size is not None:
            raise ValueError("specify either shape or size, but not both")
        # Normalize shape
        if shape is not None:
            shape = tuple(shape)
            if any(s <= 0 for s in shape):
                raise ValueError("shape must be a composition with positive parts")
        # Normalize size
        if size is not None:
            size = Integer(size)
            if size < 0:
                raise ValueError("size must be nonnegative")
        # Normalize max_entry
        if max_entry is not None:
            max_entry = Integer(max_entry)
            if max_entry < 0:
                raise ValueError("max_entry must be nonnegative")

        return super().__classcall__(cls, shape=shape,
                                     max_entry=max_entry,
                                     size=size,
                                     category=category)

    def __init__(self, shape=None, max_entry=None, size=None, category=None):
        """
        Initialize ``self``.

        INPUT:

        - ``shape`` -- optional composition shape.
        - ``max_entry`` -- optional largest allowed entry for finite generation.
        - ``category`` -- optional Sage category.

        TESTS::

            sage: QuasiRibbonTableaux(2)
            Quasi-ribbon tableaux of size 2
            sage: QuasiRibbonTableaux([1,2])
            Quasi-ribbon tableaux of shape [1, 2]
            sage: QuasiRibbonTableaux(max_entry=2)
            Quasi-ribbon tableaux with entries at most 2
        """
        # If no category is specified, use the category of sets.
        if category is None:
            category = Sets()

        # Initialize the inherited SkewTableaux parent class.
        SkewTableaux.__init__(self, category=category)

        # If shape is None, this represents quasiribbon tableaux in general.
        # If shape is given, this represents a fixed-shape family.
        self._shape = None if shape is None else Composition(shape)

        # max_entry is only used when generating finite examples.
        # Without this cutoff, there are infinitely many possible fillings.
        self._max_entry = max_entry
        self._size = size

    def _repr_(self):
        r"""
        Return a string representation of ``self``.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableaux
            sage: QuasiRibbonTableaux([1,3,1])
            Quasi-ribbon tableaux of shape [1, 3, 1]
            sage: QuasiRibbonTableaux(2)
            Quasi-ribbon tableaux of size 2
        """
        if self._shape is not None:
            if self._max_entry is None:
                return "Quasi-ribbon tableaux of shape {}".format(self._shape)
            return "Quasi-ribbon tableaux of shape {} with entries at most {}".format(
                self._shape, self._max_entry)

        if self._size is not None:
            if self._max_entry is None:
                return "Quasi-ribbon tableaux of size {}".format(self._size)
            return "Quasi-ribbon tableaux of size {} with entries at most {}".format(
                self._size, self._max_entry)

        if self._max_entry is None:
            return "Quasi-ribbon tableaux"

        return "Quasi-ribbon tableaux with entries at most {}".format(self._max_entry)

    Element = QuasiRibbonTableau

    def _an_element_(self):
        r"""
        Return an element of ``self``.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableaux
            sage: QuasiRibbonTableaux().an_element()
            [[1]]
            sage: QuasiRibbonTableaux(shape=[3, 2]).an_element()
            [[1, 1, 1], [None, None, 2, 2]]
            sage: QuasiRibbonTableaux(size=4).an_element()
            [[1, 1, 1, 1]]
        """
        if self._shape is not None:
            shape = self._shape
        elif self._size is not None:
            if self._size == 0:
                return self([])
            shape = (self._size,)
        else:
            return self([[1]])
        rows = []
        for i, row_length in enumerate(shape):
            rows.append([i + 1] * row_length)

        return self(rows)

    def shape(self):
        """
        Return the fixed composition shape of ``self``.

        Raise an error if this family does not have a fixed shape.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableaux
            sage: QRT = QuasiRibbonTableaux(shape=[3, 2])
            sage: QRT.shape()
            [3, 2]
            sage: QRT = QuasiRibbonTableaux(3)
            sage: QRT.shape()
            Traceback (most recent call last):
            ...
            ValueError: this family does not have a fixed shape
        """
        if self._shape is None:
            raise ValueError("this family does not have a fixed shape")
        return self._shape

    def tableaux_of_shape(self, shape=None, max_entry=None):
        """
        Return quasi-ribbon tableaux of a fixed shape with entries up to ``max_entry``.

        This is a small finite generator for testing.

        IMPORTANT:

        This method currently uses a brute-force approach. It tries every
        possible filling of the given shape using entries from 1 to
        the max entry. Then it constructs a tableau from each filling and keeps
        only the ones that satisfy ``is_quasi_ribbon()``.

        This is useful for small examples, but it is probably not
        efficient for large shapes or large values of ``max_entry``. In the
        future, this should probably be replaced with a smarter generation
        method that only builds fillings satisfying the row and column conditions.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableaux
            sage: QRT = QuasiRibbonTableaux()
            sage: QRT.tableaux_of_shape([2, 1], max_entry=2)
            [[[1, 1], [None, 2]]]

            sage: QRT = QuasiRibbonTableaux(shape=[2, 1])
            sage: QRT.tableaux_of_shape(max_entry=3)
            [[[1, 1], [None, 2]],
            [[1, 1], [None, 3]],
            [[1, 2], [None, 3]],
            [[2, 2], [None, 3]]]
        """
        from itertools import product
        # If the user did not pass a shape into the method, use the fixed
        # shape stored in the family object.
        if shape is None:
            shape = self._shape

        # If there is still no shape, then we do not know what fixed-shape
        # family to generate.
        if shape is None:
            raise ValueError("a shape must be specified")

        # If no max_entry is passed into the method, use the cutoff stored in
        # the family object.
        if max_entry is None:
            max_entry = self._max_entry

        if max_entry is None:
            raise ValueError("a maximum entry must be specified")

        shape = list(shape)

        total_cells = sum(shape)
        tableaux = []

        # Try every possible filling of the cells
        for filling in product(range(1, max_entry + 1), repeat=total_cells):
            pos = 0
            rows = []
            for row_length in shape:
                rows.append(list(filling[pos:pos + row_length]))
                pos += row_length
            try:
                tableaux.append(self.element_class(self,rows))
            except ValueError:
                pass
        return tableaux

    def __iter__(self):
        r"""
        Iterate over ``self``.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableaux
            sage: list(QuasiRibbonTableaux(shape=[2, 1], max_entry=2))
            [[[1, 1], [None, 2]]]
            sage: list(QuasiRibbonTableaux(size=2, max_entry=2))
            [[[1], [2]], [[1, 1]], [[1, 2]], [[2, 2]]]
        """
        if self._max_entry is None:
            raise NotImplementedError("iteration requires max_entry to be specified")

        if self._shape is not None:
            yield from self.tableaux_of_shape(self._shape, self._max_entry)
            return

        if self._size is not None:
            for shape in Compositions(self._size):
                yield from self.tableaux_of_shape(shape, self._max_entry)
            return

        raise NotImplementedError("iteration requires either shape or size to be specified")

    def list(self):
        r"""
        Return the list of quasi-ribbon tableaux in ``self``.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableaux
            sage: QuasiRibbonTableaux(shape=[2, 1], max_entry=2).list()
            [[[1, 1], [None, 2]]]
            sage: QuasiRibbonTableaux(size=2, max_entry=2).list()
            [[[1], [2]], [[1, 1]], [[1, 2]], [[2, 2]]]
        """
        if self._max_entry is None:
            raise ValueError("a maximum entry must be specified to list the tableaux")

        if self._shape is None and self._size is None:
            raise ValueError("a shape or size must be specified to list the tableaux")

        return list(self)

    def __contains__(self, x):
        r"""
        Return whether ``x`` is an element of ``self``.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableaux
            sage: QRT = QuasiRibbonTableaux()
            sage: [[1, 2], [3]] in QRT
            True

            sage: QRT = QuasiRibbonTableaux(shape=[2, 1])
            sage: [[1, 2], [3]] in QRT
            True
            sage: [[1, 2, 3]] in QRT
            False

            sage: QRT = QuasiRibbonTableaux(shape=[2, 1], max_entry=2)
            sage: [[1, 1], [2]] in QRT
            True
            sage: [[1, 1], [3]] in QRT
            False
        """
        if isinstance(x, QuasiRibbonTableau):
            Q = x
        else:
            try:
                Q = QuasiRibbonTableau(x)
            except (TypeError, ValueError):
                return False

        if (self._shape is not None
                and Q.to_composition() != self._shape):
            return False

        if self._max_entry is not None:
            for row in Q._clean_rows():
                for entry in row:
                    if entry > self._max_entry:
                        return False

        return True

    def cardinality(self):
        r"""
        Return the cardinality of ``self``.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableaux
            sage: QuasiRibbonTableaux().cardinality()
            +Infinity
            sage: QuasiRibbonTableaux(shape=[2, 1]).cardinality()
            +Infinity
            sage: QuasiRibbonTableaux(shape=[2, 1], max_entry=2).cardinality()
            1
        """
        if self._max_entry is None:
            return infinity
        elif self._shape is None and self._size is None:
            return infinity
        return Integer(len(list(self)))

    def insert_word(self, word):
        """
        Insert the letters of ``word`` one at a time into ``self``.

        EXAMPLES::

            sage: from sage.combinat.quasi_ribbon_tableau import QuasiRibbonTableaux
            sage: H = QuasiRibbonTableaux()
            sage: H.insert_word([])
            []
            sage: H.insert_word([3, 4])
            [[3, 4]]
            sage: H.insert_word([4, 3])
            [[3], [4]]
            sage: H.insert_word([1, 3, 2, 4, 4])
            [[1, 2], [None, 3, 4, 4]]
        """
        Q = QuasiRibbonTableau([])
        Q = Q.insert_word(word)
        return Q
