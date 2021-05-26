import itertools, regina
from tessellation import Tesselleted_manifold, Tesselleted_manifold_isometry, Tesselleted_manifold_isometry_group
from regina import Perm4
from P5 import P5, P5_iso, I, J, K, rt
from sage.all import QuaternionAlgebra, Matrix


def get_S5():
    """
    Returns a 5-dimensional sphere, using two copies of P5 glued via identity.
    """
    def pasting_map_sphere(facet):
        p = facet.pol
        manifold = p.manifold
        id = P5_iso()
        return (manifold.polytopes[1-p.index], id)

    return Tesselleted_manifold(P5, [0,1], pasting_map_sphere)

def get_M5():
    """
    Returns the manifold obtained with 2^8 copies of P5, induced by the coloring of P5 with 8 colors.
    """
    def pasting_map_M5(facet):
        p = facet.pol
        manifold = p.manifold
        x = list(p.index)
        id = P5_iso()
        x[facet.color] = 1 - x[facet.color]
        return (manifold.polytopes[tuple(x)], id)

    return Tesselleted_manifold(P5, [x for x in itertools.product(*[[0,1]]*8)], pasting_map_M5)

# Action of Q_8 on P5
q8_iso = {1: P5_iso(), -1: P5_iso([-1, -1, -1, -1]), I: P5_iso([1, -1, 1, -1], Perm4(3, 2, 1, 0)), J: P5_iso([1, -1, -1, 1], Perm4(1, 0, 3, 2))}
q8_iso[K] = q8_iso[I] * q8_iso[J]
for i in [I, J, K]:
    q8_iso[-i] = q8_iso[i].inverse()

# Isometry which inverts the small cusps of P5
quotienting_iso = P5_iso(refl=[1, -1, -1, -1], perm=Perm4(0,2,1,3))

def get_minimal_quotient():
    """
    Constructs a small manifold gluing two copies of P5, using Q8.
    The result is isomorphic to the manifold constructed by Ratcliffe and Tschantz.
    """
    def facet_state(facet):
        if facet.pol.index[0] % 2 == 0:
            return facet.label in {1, I, J, K}
        else:
            return facet.label in {-1, I, J, K}

    def pasting_map_minimal_quotient(facet):
        p = facet.pol
        manifold = p.manifold
        level, rotation = p.index

        if level % 2 == 0:
            if level==2 and facet.state:
                return None
            iso = q8_iso[{1: 1, -1: 1, I: J, -I: J, J: K, -J: K, K: I, -K: I}[facet.label]]
            new_p = manifold.polytopes[(level + (1 if facet.state else -1), rotation * (I if facet.index[4] == 1 else -I))]
            return (new_p, iso)

        else:
            if level==-1 and not facet.state:
                return None
            iso = q8_iso[{1: 1, -1: 1, I: -K, -I: -K, J: -I, -J: -I, K: -J, -K: -J}[facet.label]]
            new_p = manifold.polytopes[(level + (1 if facet.state else -1), rotation * (-I if facet.index[4] == 1 else I))]
            return (new_p, iso)

    mnf = Tesselleted_manifold(P5, [(-1, I), (-1, -I), (0, 1), (0, -1), (1, I), (1, -I), (2, 1), (2, -1)], pasting_map_minimal_quotient, facet_state)
    isom = Tesselleted_manifold_isometry(mnf, mnf.polytopes[(0,1)], mnf.polytopes[(1, I)], quotienting_iso)
    return mnf.get_quotient(Tesselleted_manifold_isometry_group(isom))


def get_M5_cyclic_covering():
    """
    Returns the cyclic covering of M5, given by the choice of a state on
    each facet of P5.
    """
    def facet_state(facet):
        # Sets the facet's state
        res = facet.label in {1, I, J, K}
        if facet.pol.index[facet.color] == 1:
            res = not res
        if facet.pol.index[(facet.color + 4) % 8] == 1:
            res = not res
        return res

    def pasting_map_leveled_M5(facet):
        p = facet.pol
        manifold = p.manifold
        x = list(p.index[0:8])
        level = p.index[8]

        new_level = level + (1 if facet.state else -1)

        if new_level not in {0, 1, 2}:
            return None

        id = P5_iso()
        x[facet.color] = 1 - x[facet.color]
        return (manifold.polytopes[tuple(x) + (new_level, )], id)

    return Tesselleted_manifold(P5, [x for x in itertools.product(*[[0,1]]*8 + [[1, 0, 2]]) if sum(x) % 2 == 0], pasting_map_leveled_M5, facet_state)

def get_M5_two_quotient():
    """
    Returns the quotient of the cyclic covering of M5 by the action of Q8 and the
    additional isometry which inverts the two small cusps.
    The result is isomorphic to the manifold constructed by Ratcliffe and Tschantz.
    """
    leveled_M5 = get_M5_cyclic_covering()
    isometries = [
        Tesselleted_manifold_isometry(leveled_M5, leveled_M5.polytopes[(0,)*9], leveled_M5.polytopes[x], y) for x, y in [
            ((1,1,0,0,1,1,0,0,0), P5_iso()),
            ((1,0,1,0,1,0,1,0,0), P5_iso()),
            ((1,0,0,1,1,0,0,1,0), P5_iso()),
            ((1,0,1,0,0,0,0,0,0), q8_iso[I]),
            ((1,0,0,1,0,0,0,0,0), q8_iso[J]),
            ((1,0,0,0,0,0,0,0,1), quotienting_iso)
        ]
    ]
    G = Tesselleted_manifold_isometry_group(*isometries, iterations=3)
    return leveled_M5.get_quotient(G)


def get_rt_minimal_manifold():
    """
    Constructs the manifold described by Ratcliffe and Tschantz.
    """
    def pasting_map_rt(facet):
        p = facet.pol
        number = facet.number + 16*p.index
        target_number = rt["mappings"][number]
        def get_matrix(i,j):
            standard_reflection = p.facets[(-1, 1, -1, -1, -1)].reflection_matrix
            return p.facet_from_number(j % 16).reflection_matrix * \
                (standard_reflection if j >= 16 else Matrix.identity(6)) * \
                Matrix(rt["pasting_matrices"][str(i)]) * \
                (standard_reflection if i >= 16 else Matrix.identity(6))

        m = get_matrix(number, target_number) if str(number) in rt["pasting_matrices"] else get_matrix(target_number, number).inverse()
        try:
            iso = P5_iso.from_lorentzian_matrix(m)
        except:
            raise Exception("Cannot paste {} to {}".format(number, target_number))
        return (p.manifold.polytopes[1 if target_number >= 16 else 0], iso)

    return Tesselleted_manifold(P5, [0,1], pasting_map_rt)
