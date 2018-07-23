from copy import deepcopy
from itertools import chain
from collections import Counter, OrderedDict
from util.layer_state import LayerState
from util.graph_spec import *


# build_layer returns a dict containining all the verticesand edges at particular E-Outerplanarity.
def build_layer(blank_verts, remove):
    vertices = dict()
    for v, u in remove:
        if v not in vertices:
            vertices[v] = deepcopy(blank_verts[v])
        if u not in vertices:
            vertices[u] = deepcopy(blank_verts[u])
        vertices[v].add_edge(u)
        vertices[u].add_edge(v)
    return vertices


# remove_layer is the inverse function to build_layer and removes all the edges from a list of vertices at a partiulcar E-Outerplanarity level.
def remove_layer(vertices, remove):
    for v, u in remove:
        vertices[v].remove_edge(u)
        vertices[u].remove_edge(v)


def parse_cycles(vertices, visited, edges_traversed):
    count = Counter(edges_traversed)
    visited = set(visited)
    marked = set()
    cycles = []
    cycle_verts = set()
    # Do a DFS at vertex, without crossing any edges that we previously traversed twice.
    # However, we will visit each vertex at most once, as if we traverse a vertex during a BFS
    # We do not need to start a BFS at that vertex.
    for v in visited:
        if v in marked:
            continue

        new_cycle = set()
        current = v

        while True:
            marked.add(current)
            stop = False
            for u in vertices[current]:
                edge = (min(current, u), max(current, u))
                # For all edges traversed, if the edge was traversed once the
                # edge is part of a cycle. Otherwise, the edge is part of a tree.
                if count[edge] == 2 or u in marked:
                    continue
                new_cycle.add(edge)
                current = u
                cycle_verts.add(current)
                break
            else:
                stop = True
            if stop:
                break

        if current == v:
            continue
        cycle_verts.add(v)
        new_cycle.add((min(current, v), max(current, v)))
        cycles.append(new_cycle)

    return cycles, cycle_verts


def parse_trees(vertices, visited, edges_traversed, cycles, cycle_verts):
    # To determine the vertices of a particular cycle or tree, begin a
    # depth-first search at both endpoints of a tree or cycle edge and traverse
    # every edge adjacent of the same type. Two cycles or two trees will never
    # share the same vertex, so the depth-first search will traverse the entire
    # tree or cycle and then end.
    cycle_verts = set(cycle_verts)
    trees = []
    support_sets = []
    marked = deepcopy(cycle_verts)
    flat_cycles = set(chain(*cycles))

    # Like above we can do a simple BFS, but we must also keep track of when we
    # hit a cycle vertex.
    for v in visited:
        if v in marked:
            continue
        new_tree = set()
        to_visit = [v]
        support = set()
        while to_visit != []:
            current = to_visit.pop()
            marked.add(current)
            for u in vertices[current]:
                new_tree.add((min(current, u), max(current, u)))
                # For all vertices that have two incident cycle edges, if the
                # tree edge is on the same E-outerplanarity as the vertex, then
                # it is an outward cycle vertex. Otherwise, then it is an
                # inward cycle vertex.
                if u in cycle_verts:
                    support.add(u)
                elif not u in marked:
                    to_visit.append(u)
        trees.append(new_tree)
        support_sets.append(support)

    # We miss a single edge tree if it is between two cycles, so catch those.
    flat_trees = set(chain(*trees))
    for v in cycle_verts:
        for u in vertices[v]:
            edge = (min(u, v), max(u, v))
            if edge in flat_cycles or edge in flat_trees or u < v:
                continue
            trees.append(set([edge]))
            support_sets.append({u, v})
    return trees, support_sets


def start_phase(full_vertices, blank_verts):
    path = [upper_left_most(full_vertices, range(len(full_vertices)))]
    # Let the current E-outerplanarity level be 0
    planarity = 0

    # By marking edges at each E-outerplanarity layer one at a time
    # the trees and cycles can be differentiated.
    layer_states = []
    while path:
        remove_set = set()
        # n_path will be a nested list of lists (but we cannot flatten it just
        # yet).
        n_path = []
        remove = []
        n_visited = []
        all_edges_traversed = []
        layers_paths = []
        cycles = []
        trees = []
        supports = []
        cycle_verts = set()
        vertex_to_cycle_above = dict()

        ls_a = None
        if len(layer_states) > 0:
            ls_a = layer_states[-1]

        # The edge of this particular E-outerplanarity are now, defined to be
        # all the edges traversed which are contained in path.
        for v in path:
            if len(full_vertices[v]) != 0 and v not in remove_set:
                current_path, current_remove, edges_traversed = outer_face(
                    full_vertices, v)

                layers_paths.append(current_path)
                all_edges_traversed.append(edges_traversed)
                n_path.append(current_path)
                remove += current_remove

                for w, u in current_remove:
                    remove_set.add(w)
                    remove_set.add(u)
                    if ls_a:
                        c = ls_a.vertex_to_cycle[v]
                        vertex_to_cycle_above[w] = c
                        vertex_to_cycle_above[u] = c

        path = list(chain(*n_path))

        remove_layer(full_vertices, remove)

        vertices = build_layer(blank_verts, remove)

        all_degree_two = True
        for v in path:
            all_degree_two = all_degree_two and len(vertices[v]) == 2

        # If the planarity is 0 and every vertex is degree two then that means
        # that this layer is a single cycle and we can add the cycle_vertices
        # appropriately.
        if planarity == 0 and all_degree_two:
            new_cycle = set()
            for i in range(len(path) - 1):
                u = path[i]
                v = path[i + 1]
                new_cycle.add((min(u, v), max(u, v)))
                cycle_verts.add(u)

            new_cycle.add((min(path[0], path[-1]), max(path[0], path[-1])))
            cycle_verts.add(path[-1])
            cycles.append(new_cycle)

        else:
            for i, edges in enumerate(all_edges_traversed):
                n_cycles, n_cycle_verts = parse_cycles(vertices, n_path[i],
                                                       edges)
                n_trees, n_supports = parse_trees(vertices, n_path[i], edges,
                                                  n_cycles, n_cycle_verts)
                cycles += n_cycles
                trees += n_trees
                supports += n_supports
                cycle_verts.update(n_cycle_verts)

        layer_states.append(
            LayerState(vertices, cycles, cycle_verts, trees, supports,
                       layers_paths, vertex_to_cycle_above))

        # Increment the E-outerplanarity by 1
        planarity += 1

    for i, ls in enumerate(layer_states[1:]):
        ls.set_path_above(layer_states[i])
    # We actual overcount the planarity by 1, because we run once with 
    # path = [] for a full go before the loop terminates.
    planarity -= 1
    return planarity, layer_states
