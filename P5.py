import itertools, json, os, sys
from typing import Dict, List, Literal, Tuple
from sage.all import product, QuaternionAlgebra, Matrix, Permutation, vector, Graph
from regina import Perm4, Perm5, Perm6, Triangulation5
from tessellation import AbstractPolytopeIsometry, AbstractPolytope, AbstractFacet

Quaternions = QuaternionAlgebra(-1, -1)
I, J, K = Quaternions.gen(0), Quaternions.gen(1), Quaternions.gen(2)

with open(os.path.join(sys.path[0], "ratcliffe-tschantz.json")) as f:
    rt = json.load(f)
    for m in rt["pasting_matrices"].values():
        assert (
            Matrix(m).transpose() * Matrix.diagonal([1, 1, 1, 1, 1, -1]) * Matrix(m)
        ) == Matrix.diagonal([1, 1, 1, 1, 1, -1]), m


class P5_iso(AbstractPolytopeIsometry):
    """
    Defines an isomophism of P5.
    It is descibed by the composition of reflections on coordinate
    hyperplanes and permutations of coordinates.

    Args:
        refl: a list of 5 signs, one for each coordinate hyperplane
        perm: a permutation of the coordinates
    """

    def __init__(
        self, refl: List[Literal[1, -1]] = [1, 1, 1, 1, 1], perm: Perm5 = Perm5()
    ):
        if len(refl) == 4:
            refl.append(product(refl))
        assert len(refl) == 5 and product(refl) == 1, "Invalid reflection"
        self.refl = refl

        if isinstance(perm, Perm4):
            perm = Perm5.extend(perm)
        assert isinstance(perm, Perm5)
        self.perm = perm

    def inverse(self):
        """
        Returns the inverse isomorphism.
        """
        phi = P5_iso(perm=self.perm.inverse())
        psi = P5_iso(self.refl)
        inv = phi * psi
        # Check composition is the identity
        assert inv * self == P5_iso(), (inv, self)
        return inv

    @classmethod
    def from_lorentzian_matrix(cls, mat: Matrix[5, 5, int]) -> "P5_iso":
        """
        Returns the isomorphism corresponding to the given
        Lorentzian matrix.

        Args:
            mat: a 5x5 matrix with determinant 1 and signature (4,1)
        """
        cusps = [vector({i: 1, 5: 1}) for i in range(5)]
        cusps += [vector([1, 1, 1, 1, 1, 3]) - x for x in cusps]
        assert sorted(cusps) == sorted(mat * v for v in cusps), mat
        return cls(perm=Perm5(*[cusps.index(mat * v) % 5 for v in cusps[0:5]])) * cls(
            refl=[1 if mat * v in cusps[0:5] else -1 for v in cusps[0:5]]
        )

    def __eq__(self, other):
        return self.perm == other.perm and self.refl == other.refl

    def __mul__(self, other):
        return P5_iso(
            [self.refl[i] * other.refl[self.perm.pre(i)] for i in range(5)],
            self.perm * other.perm,
        )

    def __repr__(self):
        return str((self.refl, self.perm))

    def __call__(self, arg, other_pol=None):
        # Return corresponding facet via isometry
        if other_pol is None:
            other_pol = arg.pol

        # Pemutates coordinates
        coords = tuple(arg.index[self.perm.pre(i)] for i in range(5))

        # Reflect coordinates
        coords = tuple(x * y for x, y in zip(self.refl, coords))

        if isinstance(arg, P5_facet):
            return other_pol.facets[coords]
        else:
            raise TypeError("Invalid argument for isometry")


class P5_facet(AbstractFacet):
    pol: "P5"

    def triangulate(self, tri: Triangulation5):
        """
        Triangulates the cone on a facet of P5 with six simplices:
        a central one and five attached to the facets of the central
        one (all but one, which coincides with the external facet of
        P5).
        The vertex 0 always corresponds to the vertex in the center
        of P5.
        """
        self.simplices = [tri.newSimplex() for _ in range(6)]

        for i in range(1, 6):
            self.simplices[0].join(i, self.simplices[i], Perm6())

    def interior_join(self, other_facet: "P5_facet"):
        """
        Pastes together two triangulations of two adiacents facets
        of the same P5.
        Two such triangulations are adjacent in two pairs of simplices,
        corresponding to the two directions where the signs of the
        standard facet labelling differ.
        """
        a, b = (i + 1 for i in range(5) if self.index[i] != other_facet.index[i])
        self.simplices[a].join(b, other_facet.simplices[b], Perm6(a, b))
        self.simplices[b].join(a, other_facet.simplices[a], Perm6(a, b))

    def interior_unjoin(self, other_facet: "P5_facet"):
        """
        Unglue two facets which were adjacent in the same P5.
        """
        a, b = (i + 1 for i in range(5) if self.index[i] != other_facet.index[i])
        self.simplices[a].unjoin(b)
        self.simplices[b].unjoin(a)

    def exterior_join(self, other_pol: "P5", iso: P5_iso) -> None:
        target_f = iso(self, other_pol)
        extended_perm = (
            Perm6([1, 2, 3, 4, 5, 0])
            * Perm6.extend(iso.perm)
            * Perm6([5, 0, 1, 2, 3, 4])
        )
        for i in range(6):
            if self.simplices[i].adjacentSimplex(0) is None:
                self.simplices[i].join(
                    0, target_f.simplices[extended_perm[i]], extended_perm
                )
            else:
                assert (
                    self.simplices[i].adjacentSimplex(0)
                    == target_f.simplices[extended_perm[i]]
                )
                assert self.simplices[i].adjacentGluing(0) == extended_perm

    def get_color(self) -> int:
        """
        Returns the color of the face.
        """
        dict: Dict[Tuple, int] = {
            (1, 1, 1, 1): 0,
            (-1, 1, 1, 1): 4,
            (1, -1, 1, 1): 5,
            (1, -1, 1, -1): 1,
            (1, 1, -1, 1): 6,
            (1, -1, -1, 1): 2,
            (1, 1, 1, -1): 7,
            (1, 1, -1, -1): 3,
        }
        x = self.index[0:4]
        if x in dict:
            return dict[x]
        else:
            return dict[tuple(-i for i in x)]

    color = property(get_color)

    def get_label(self):
        """
        Returns a labelling in Q8.
        """
        dict = {
            (1, 1, 1, 1): 1,
            (-1, 1, 1, 1): 1,
            (1, -1, 1, 1): I,
            (1, -1, 1, -1): I,
            (1, 1, -1, 1): J,
            (1, -1, -1, 1): J,
            (1, 1, 1, -1): K,
            (1, 1, -1, -1): K,
        }
        x = self.index[0:4]
        if x in dict:
            return dict[x]
        else:
            return -dict[tuple(-i for i in x)]

    label = property(get_label)

    def get_reflection_matrix(self) -> Matrix[6, 6, int]:
        """
        Returns a reflection matrix representing the
        reflection along this facet, using Ratcliffe
        and Tschantz description.
        """
        if self.index == (1, 1, 1, 1, 1):
            res = Matrix(rt.get("reflection_matrices")[2])
        elif sum(self.index) == 1:
            perm = Permutation(
                sorted(range(1, 6), key=lambda x: -self.index[x - 1])
            ).inverse()
            res = Matrix(rt.get("reflection_matrices")[1])
            res.permute_rows_and_columns(perm, perm)
        elif sum(self.index) == -3:
            perm = Permutation(
                sorted(range(1, 6), key=lambda x: -self.index[x - 1])
            ).inverse()
            res = Matrix(rt.get("reflection_matrices")[0])
            res.permute_rows_and_columns(perm, perm)
        else:
            raise Exception("Unexpected index for this facet")
        assert res.transpose() * Matrix.diagonal(
            [1, 1, 1, 1, 1, -1]
        ) * res == Matrix.diagonal([1, 1, 1, 1, 1, -1])
        return res

    reflection_matrix = property(get_reflection_matrix)

    def get_number(self):
        """
        Returns a canonical numerical id for the facet.
        """
        return sorted(
            [c for c in self.pol.facets], key=lambda x: (sum(x), [-i for i in x])
        ).index(self.index)

    number = property(get_number)


class P5(AbstractPolytope):
    dimension = 5
    facet_class = P5_facet
    facet_graph = Graph(
        [
            {t for t in itertools.product(*[[1, -1]] * 5) if product(t) == 1},
            lambda x, y: sum(i * j for i, j in zip(x, y)) == 1,
        ]
    )

    def facet_from_number(self, n):
        """
        Returns the n-th facet of P5, according to the canonical sorting.
        """
        return self.facets[
            sorted([c for c in self.facets], key=lambda x: (sum(x), [-i for i in x]))[n]
        ]
