r"""
Feature for testing the presence of libbraiding
"""

from sage.features.join_feature import JoinFeature
from sage.features import PythonModule


class Libbraiding(JoinFeature):
    r"""
    A :class:`sage.features.Feature` describing the presence of
    :mod:`sage.libs.braiding`, the interface to braid groups via
    libbraiding.

    TESTS::

        sage: from sage.features.libbraiding import Libbraiding
        sage: Libbraiding().is_present()  # needs libbraiding
        FeatureTestResult('libbraiding', True)
        sage: Libbraiding().is_present()  # needs !libbraiding
        FeatureTestResult('sage.libs.braiding', False)

    """
    def __init__(self):
        r"""
        TESTS::

            sage: from sage.features.libbraiding import Libbraiding
            sage: isinstance(Libbraiding(), Libbraiding)
            True

        """
        JoinFeature.__init__(self, 'libbraiding',
                             [PythonModule('sage.libs.braiding')],
                             spkg='libbraiding', type='standard')


def all_features():
    return [Libbraiding()]
