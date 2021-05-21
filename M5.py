import itertools, regina
from tessellation import Tesselleted_manifold, Tesselleted_manifold_isometry, Tesselleted_manifold_isometry_group
from regina import Perm4
from P5 import P5, P5_iso, I, J, K
from sage.all import QuaternionAlgebra


def get_S5():
    def pasting_map_sphere(facet):
        p = facet.pol
        manifold = p.manifold
        id = P5_iso()
        return (manifold.polytopes[1-p.index], id)

    return Tesselleted_manifold(P5, [0,1], pasting_map_sphere)

def get_M5():
    def pasting_map_M5(facet):
        p = facet.pol
        manifold = p.manifold
        x = list(p.index)
        id = P5_iso()
        x[facet.color] = 1 - x[facet.color]
        return (manifold.polytopes[tuple(x)], id)

    return Tesselletde_manifold(P5, [x for x in itertools.product(*[[0,1]]*8)], pasting_map_M5)

# Isometrie date da Q8
q8_iso = {1: P5_iso(), -1: P5_iso([-1, -1, -1, -1]), I: P5_iso([1, -1, 1, -1], Perm4(3, 2, 1, 0)), J: P5_iso([1, -1, -1, 1], Perm4(1, 0, 3, 2))}
q8_iso[K] = q8_iso[I] * q8_iso[J]
for i in [I, J, K]:
    q8_iso[-i] = q8_iso[i].inverse()

# Definisco l'isometria che incolla due poliedri di livelli diversi.
quotienting_iso = P5_iso(refl=[1, -1, -1, -1], perm=Perm4(0,2,1,3))

def get_minimal_quotient():

    def pasting_map_minimal_quotient(facet):
        """
        Mappa di incollamento per la varietà con due poliedri.
        """
        p = facet.pol
        manifold = p.manifold
        level, rotation = p.index

        if level % 2 == 0:
            state_in = facet.label in {-1, -I, -J, -K}
            if level==2 and state_in:
                return None
            iso = q8_iso[{1: 1, -1: 1, I: J, -I: J, J: K, -J: K, K: I, -K: I}[facet.label]]
            new_p = manifold.polytopes[(level + (1 if state_in else -1), rotation * (I if facet.coords[4] == 1 else -I))]
            new_f = iso(facet, new_p)
            # Qualche check di coerenza
            assert state_in == (new_f.label in {-1, I, J, K}), (facet.label, new_f.label)
            return (new_p, iso)

        else:
            state_in = facet.label in {1, -I, -J, -K}
            if level==-1 and not state_in:
                return None
            iso = q8_iso[{1: 1, -1: 1, I: -K, -I: -K, J: -I, -J: -I, K: -J, -K: -J}[facet.label]]
            new_p = manifold.polytopes[(level + (1 if state_in else -1), rotation * (-I if facet.coords[4] == 1 else I))]
            new_f = iso(facet, new_p)
            # Qualche check di coerenza
            assert state_in == (new_f.label in {1, I, J, K}), (facet.label, new_f.label)
            return (new_p, iso)

    minimal_quotient = Tesselleted_manifold(P5, [(-1, I), (-1, -I), (0, 1), (0, -1), (1, I), (1, -I), (2, 1), (2, -1)], pasting_map_minimal_quotient)


def get_M5_cyclic_covering():
    def pasting_map_leveled_M5(facet):
        p = facet.pol
        manifold = p.manifold
        x = list(p.index[0:8])
        level = p.index[8]

        # Sets the facet's state
        if facet.state is None:
            facet.state = facet.label in {1, I, J, K}
            if x[facet.color] == 1:
                facet.state = not facet.state
            if x[(facet.color + 4) % 8] == 1:
                facet.state = not facet.state
        new_level = level + (1 if facet.state else -1)

        if new_level not in {0, 1, 2}:
            return None

        id = P5_iso()
        x[facet.color] = 1 - x[facet.color]
        return (manifold.polytopes[tuple(x) + (new_level, )], id)

    return Tesselleted_manifold(P5, [x for x in itertools.product(*[[0,1]]*8 + [[1, 0, 2]]) if sum(x) % 2 == 0], pasting_map_leveled_M5)

def get_M5_two_quotient():
    leveled_M5 = get_M5_cyclic_covering()
    isometries = []
    isometries.append(Tesselleted_manifold_isometry(leveled_M5, leveled_M5.polytopes[(0,)*9], leveled_M5.polytopes[(1,1,0,0,1,1,0,0,0)], P5_iso()))
    isometries.append(Tesselleted_manifold_isometry(leveled_M5, leveled_M5.polytopes[(0,)*9], leveled_M5.polytopes[(1,0,1,0,1,0,1,0,0)], P5_iso()))
    isometries.append(Tesselleted_manifold_isometry(leveled_M5, leveled_M5.polytopes[(0,)*9], leveled_M5.polytopes[(1,0,0,1,1,0,0,1,0)], P5_iso()))
    isometries.append(Tesselleted_manifold_isometry(leveled_M5, leveled_M5.polytopes[(0,)*9], leveled_M5.polytopes[(1,0,1,0,0,0,0,0,0)], q8_iso[I]))
    isometries.append(Tesselleted_manifold_isometry(leveled_M5, leveled_M5.polytopes[(0,)*9], leveled_M5.polytopes[(1,0,0,1,0,0,0,0,0)], q8_iso[J]))
    isometries.append(Tesselleted_manifold_isometry(leveled_M5, leveled_M5.polytopes[(0,)*9], leveled_M5.polytopes[(1,0,0,0,0,0,0,0,1)], quotienting_iso))
    G = Tesselleted_manifold_isometry_group(*isometries, iterations=3)
    return leveled_M5.get_quotient(G)
