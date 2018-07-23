from enum import Enum, unique
from copy import deepcopy
from collections import deque
from math import pi, atan2
from util.graph_spec import upper_left_most


@unique
class Ops(Enum):
    COLLAPSE_TYPE_A = 0
    COLLAPSE_TYPE_B = 1
    MERGE_TYPE_A = 2
    MERGE_TYPE_B = 3


# The basic premise for the algorithm is to start on the outside and move
# inwards, first collapsing Type A trees and Type B trees (with singleton
# support sets) that have all their vertices in a row, and then merging these
# trees clockwise. This results in more trees that are now ready to be
# collapsed. Though it works outside in, the deeper the trees and cycles, the
# higher their priority in the queue their priority, because they are more
# recent and because cycles may be waiting for them to collapse before the
# cycle as a whole can merge.
def algorithmKS(layer_states, rs, planarity, check_valid):
    if planarity == 1:
        # Not equipped to handle planarity == 1
        assert False

    # prepare_cycle(outermost cycle enclosing the whole graph)
    prep_cycle(layer_states, 0, rs, 0)

    # While any queue is not empty, pop the oldest tree in the queue at the
    # deepest E-outerplanarity level. If the tree has not collapsed, collapse
    # the tree. Otherwise, merge the tree.
    done = False
    while not done:
        done = True
        for layer in range(planarity - 1, -1, -1):
            operations = rs.operations[layer]
            if len(operations) == 0:
                continue
            done = False
            op, arg = operations.popleft()

            if op == Ops.COLLAPSE_TYPE_A:
                collapse_type_a(layer_states, layer, rs, arg)
            elif op == Ops.COLLAPSE_TYPE_B:
                collapse_type_b(layer_states, layer, rs, arg)
            elif op == Ops.MERGE_TYPE_A:
                merge_type_a(layer_states, layer, rs, arg)
            elif op == Ops.MERGE_TYPE_B:
                merge_type_b(layer_states, layer, rs, arg)
            else:
                raise ("Invalid operation")
            break

    # AlgorithmKS has finished running, but we now test the results to confirm
    # their correctness.
    rs.build_Blst()
    if check_valid:
        validate(layer_states, rs)


def alpha_measure(rs, super_node):
    count = 0
    for v in super_node:
        for u in rs.vertices[v]:
            if not u in super_node:
                count += 1
    return count


def validate(layer_states, rs):
    # We have collapsed every vertex
    assert len(rs.collapsed) == len(rs.vertices)

    # The final super vertex contains every vertex
    assert len(rs.Blst[-1]) == len(rs.vertices)

    # Every vertex has been indexed
    assert len(rs.indx) == len(rs.vertices)

    singles = [super_set for super_set in rs.Blst if len(super_set) == 1]
    # We never collapsed a single vertex more than once
    assert len(singles) == len(rs.vertices) == len(set(singles))

    # We are never reassembling a duplicate
    assert len(set(rs.Blst)) == len(rs.Blst)

    # We are linear in terms of space complexity
    assert len(rs.Blst) <= 2 * len(rs.vertices) - 1

    alpha = 0
    for super_node in rs.Blst:
        alpha = max(alpha, alpha_measure(rs, super_node))
    # Make sure our claim that max alpha <= 2*planarity holds.
    assert alpha <= 2 * len(layer_states)


def assert_get(single_set):
    assert len(single_set) == 1
    return next(iter(single_set))


def tree_successor(layer_states, layer, rs, tree, super_v):
    def succ(u):
        # succ keeps going from a particular vertex around a cycle until it finds an inner vertex
        # or makes a full circle
        c, start = ls_a.vertex_to_cycle_index[u]
        path = ls_a.cycle_paths[c]
        i = start
        while True:
            i = (i + 1) % len(path)
            if len(ls_a.vertices[path[i]]) == 2 or i == start:
                break
        return path[i]

    ls = layer_states[layer]
    ls_a = layer_states[layer - 1]
    v_tree = ls.v_by_tree[tree]
    # To find the successor of a tree, keep going clockwise around its leaf vertices until we find
    # a node that is not ins
    alt_next_v = 0
    if len(ls.tree_to_nonconsec[tree]) == 0:
        return -1
    last_v = assert_get(ls.tree_to_nonconsec[tree])
    return succ(last_v)


# prep_cycle is the most complex function in the entire algorith. For a
# particular cycle, it adds every Type A and Type B tree to operations that is
# ready to be immediately collapsed. However, the order in which these trees
# are collapsed is crucial. If there are any Type A trees at a particular layer
# the first tree to be collapsed MUST be a Type A tree, otherwise, the last
# cycle could be merged into a Type A tree (which would add significantly more
# complexity to the merging process). Generally, less complex structures, like
# Type A, Type B (with only one cycle edge) trees—are merged into more complex
# structures—like Type C trees and cycles. Though it is usually not linear time
# to handle merging of trees, by being careful with the order, such that every
# tree (except for one) on a particular cycle is collapsed and merged before
# the next cycle is handled, a lot less information needs to be juggled and the
# complexity is reduced.
def prep_cycle(layer_states, layer, rs, cycle):
    layer = layer + 1
    # Though cycle is on layer, every tree that we wish to prepare for
    # operation is actually on layer + 1 so we adjust our frame of reference
    # one layer deeper in order to make things easier to understand.
    ls = layer_states[layer]
    ls_a = layer_states[layer - 1]
    cycle_to_type_b_count = dict()
    path = ls_a.cycle_paths[cycle]
    last_v_with_tree = -1
    start_cycle = -1
    marked_trees = set()
    tree_to_leaf_count = dict()
    rs.dir_G[path[0]].remove_edge(path[-1])
    for i, v in enumerate(path):
        if i < len(path) - 1:
            rs.dir_G[path[i + 1]].remove_edge(v)

        if not v in ls.vertex_to_tree:
            continue
        t = ls.vertex_to_tree[v]
        if not t in tree_to_leaf_count:
            tree_to_leaf_count[t] = 0
        tree_to_leaf_count[t] += 1

        if len(ls.supports[t]) != 1:
            continue
        u = next(iter(ls.supports[t]))
        c = ls.vertex_to_cycle[u]
        last_v_with_tree = v
        start_cycle = c
        if t in marked_trees:
            continue
        marked_trees.add(t)
        if not c in cycle_to_type_b_count:
            cycle_to_type_b_count[c] = 0
        cycle_to_type_b_count[c] += 1

    # Go counterclockwise from the first vertex until we find a different tree
    # than the one we started on. That way, when we go clockwise from that
    # point we can be sure every tree has all of its vertices in a row when it
    # is collapsed.
    if last_v_with_tree == -1:
        for v in path:
            if not v in ls.vertex_to_tree:
                continue
            t = ls.vertex_to_tree[v]
            tree_to_leaf_count[t] -= 1
            if tree_to_leaf_count[t] != 0:
                continue
            if t in marked_trees or len(ls.supports[t]) != 0 or len(
                    ls.tree_to_nonconsec[t]) > 1:
                continue
            rs.operations[layer].append((Ops.COLLAPSE_TYPE_A, t))
            marked_trees.add(t)
        return

    _, i = ls_a.vertex_to_cycle_index[last_v_with_tree]
    start = i
    # We find the next tree that has support set > 1 or a support set 1 and a
    # different support cycle.
    while True:
        i = (i + 1) % len(path)
        v = path[i]
        if i == start:
            break
        if v not in ls.vertex_to_tree:
            continue
        t = ls.vertex_to_tree[v]
        if len(ls.supports[t]) == 0:
            continue
        if len(ls.supports[t]) > 1:
            break
        v = next(iter(ls.supports[t]))
        c = ls.vertex_to_cycle[v]
        if c != start_cycle:
            break

    # Now we can find a cycle that has all of its Type B single support trees
    # in a row and start the path at the first Type B tree.
    path = path[i:] + path[:i]
    current_cycle = None
    start = None
    for i, v in enumerate(path):
        if not v in ls.vertex_to_tree:
            continue
        t = ls.vertex_to_tree[v]
        if len(ls.supports[t]) != 1:
            continue
        u = next(iter(ls.supports[t]))
        c = ls.vertex_to_cycle[u]
        if c != current_cycle:
            current_cycle = c
            start = i
        cycle_to_type_b_count[c] -= 1
        if cycle_to_type_b_count[c] == 0:
            break

    # Finally, if it is possible to start at a Type A tree without crossing to
    # another cycle we do so.
    path = path[start:] + path[:start]
    marked_trees = set()
    start = i
    possible = False
    for i, v in enumerate(path):
        if not v in ls.vertex_to_tree:
            continue
        t = ls.vertex_to_tree[v]
        if len(ls.supports[t]) == 0:
            possible = True
            break
        if len(ls.supports[t]) == 1:
            u = next(iter(ls.supports[t]))
            c = ls.vertex_to_cycle[u]
            if c != current_cycle:
                possible = False
                break

    if possible:
        path = path[i:] + path[:i]

    # Now we collapse Type B trees in a clockwise order with respect to cycle.
    # However, if there is a predecessor to a particular tree A with respect to
    # tree B single support cycle, we will collapse that tree, even if A is
    # clockwise after B with respect to cycle.
    to_collapse_total = []
    for v in path:
        if not v in ls.vertex_to_tree:
            continue
        t = ls.vertex_to_tree[v]
        if t in marked_trees:
            continue
        tree_to_leaf_count[t] -= 1
        if tree_to_leaf_count[t] > 0 or len(ls.tree_to_nonconsec[t]) > 1:
            continue

        if len(ls.supports[t]) == 0:
            rs.operations[layer].append((Ops.COLLAPSE_TYPE_A, t))
            marked_trees.add(t)
        if len(ls.supports[t]) != 1:
            continue

        u = next(iter(ls.supports[t]))
        c, start = ls.vertex_to_cycle_index[u]

        support_path = ls.cycle_paths[c]
        index = start
        t_ordered = deque([t])
        # We found a tree to collapse, but most traverse counterclockwise on its support cycle
        # in order to collapse the tree's successor before we collapse the tree itself.
        while True:
            index = (index - 1) % len(support_path)
            v = support_path[index]
            if not v in ls.vertex_to_tree:
                break

            t = ls.vertex_to_tree[v]
            if len(ls.supports[t]) != 1 or t in marked_trees:
                break
            if index == start:
                # There is no true order here, so just follow clockwise, and drop all of our predecessors
                t_ordered = deque([t])
                break
            t_ordered.append(t)

        while len(t_ordered) != 0:
            t = t_ordered.pop()
            marked_trees.add(t)
            rs.operations[layer].append((Ops.COLLAPSE_TYPE_B, t))


# merge cycle is called when we have no incident trees on this cycle that have not been collapsed.
# So we find a tree incident to this cycle that has a successor that has not merged yet
# then merge into that. If there is no such tree, then we esclated this super to the cycle above us
def merge_cycle(layer_states, layer, rs, c, super_v):
    ls = layer_states[layer]
    ls_a = layer_states[layer - 1]
    found = False
    next_t = None

    # Find the clockwise successor tree of this cycle on the layer enclosing this one.
    for v in ls.cycle_paths[c]:
        if not v in ls.vertex_to_tree:
            continue
        t = ls.vertex_to_tree[v]
        u = tree_successor(layer_states, layer, rs, t, super_v)
        if not u in ls.vertex_to_tree:
            continue
        next_t = ls.vertex_to_tree[u]
        if next_t in rs.tree_has_merged[layer]:
            continue

        found = True
        break
    # If there is such a tree, merge super and the vertex closest to this cycle.
    if found:
        s = len(ls.supports[next_t])
        # Type A trees all should have been collapsed and merged on a particular cycle before the
        # first cycle is ready to merge.
        assert s != 0
        if s == 1:
            u = next(iter(ls.supports[next_t]))
            rs.merge_vertex_to_super_out(u, super_v)
        else:
            # Should not be merging into such a tree (But if we are then maybe we can just push into the super)
            assert False
        return

    # Otherwise, if the outer cycle is the outermost cycle, the graph has been fully collapsed and no more work is left. We have completed the graph!
    if layer == 1:
        return

    # Otherwise, we escalate, and check if we left a tree incident
    # If not then it it time for merge_tree again
    v = ls.cycle_paths[c][0]
    # Refer to the cycle enclosing c as outer_cycle
    outer_cycle = ls.vertex_to_cycle_above[v]

    # Otherwise, if the outer cycle has any incident trees left uncollapsed
    if len(ls_a.trees_by_cycle[outer_cycle]) != 0:
        # It will have exactly one incident tree left uncollapsed.
        # prepare_incident_tree(the outer cycle, super)
        prep_incident_tree(layer_states, layer - 1, rs, outer_cycle, super_v)
    # Otherwise, we must recurse upwards to continue.
    else:
        # merge_cycle(the outer cycle, super)
        merge_cycle(layer_states, layer - 1, rs, outer_cycle, super_v)


def prep_incident_tree(layer_states, layer, rs, c, super_v):
    ls = layer_states[layer]
    # There is exactly one tree uncollapsed incident to c
    incident_tree = assert_get(ls.trees_by_cycle[c])
    v = ls.tree_cycle_to_support_vertex[(incident_tree, c)]
    # We now have the support vertex on this cycle of the last incident tree,
    # and the super that should merge into it, so we do that now.
    #  Merge cycle and the root vertex of the incident tree on cycle
    rs.merge_to_super_in(v, super_v)
    ls.supports[incident_tree].remove(v)
    if len(ls.supports[incident_tree]) != 1:
        return
    if incident_tree in rs.tree_will_collapse[layer]:
        return
    if len(ls.tree_to_nonconsec[incident_tree]) > 1:
        return
    # If the incident tree is ready to collapse, add the incident tree to the queue for this layer so it as a type B tree.
    rs.tree_will_collapse[layer].add(incident_tree)
    rs.operations[layer].append((Ops.COLLAPSE_TYPE_B, incident_tree))


def collapse_type_a(layer_states, layer, rs, tree):
    # The collapsing of the tree is handled by collapse_tree, however a lot of data structures
    # are keeping track of both the trees and individual vertices that have been collapsed
    # so we update those here.
    ls = layer_states[layer]
    v_tree = ls.v_by_tree[tree]
    # Refer to the upper left most vertex of tree as start
    start = upper_left_most(ls.vertices, v_tree)
    # Collapse_tree(tree,v)
    super_v = collapse_tree(ls.vertices, start, v_tree, rs)
    rs.tree_has_collapsed[layer][tree] = True

    rs.tree_to_super_out[layer][tree] = super_v
    ls_a = layer_states[layer - 1]
    v = next(iter(v_tree))
    c = ls.vertex_to_cycle_above[v]
    for v in v_tree:
        rs.collapsed.add(v)
        # If we are not at least at layer 2 depth, we are not within a cycle that can contain an incident tree
        if layer < 2 or len(ls.vertices[v]) != 1:
            continue

        rs.collapsed_by_cycle[layer - 1][c].add(v)

    # Add tree to the queue for this layer so it merges as a type A tree
    rs.operations[layer].append((Ops.MERGE_TYPE_A, tree))


def collapse_type_b(layer_states, layer, rs, tree):
    ls = layer_states[layer]
    if len(ls.supports[tree]) == 0:
        # Because all supports of this Type B tree were collapsed at the same time,
        # we can handle it as a Type A, which we will do immmediately to preserve order.
        collapse_type_a(layer_states, layer, rs, tree)
        return
    v_tree = ls.v_by_tree[tree]

    # Refer to the root of tree as v
    v = assert_get(ls.supports[tree])
    # collapse_tree(tree,v)
    super_v = collapse_tree(ls.vertices, v, v_tree, rs)
    rs.tree_has_collapsed[layer][tree] = True

    for u in v_tree:
        if u != v:
            # We will add the support vertex to collapsed when we merge this tree
            rs.collapsed.add(u)

    c = ls.vertex_to_cycle[v]
    rs.vertex_to_super_out[v] = super_v

    # Add tree to the queue for this layer so it merges as a type B tree
    rs.operations[layer].append((Ops.MERGE_TYPE_B, v))


def merge_type_a(layer_states, layer, rs, tree):
    def succ(u):
        c, start = ls_a.vertex_to_cycle_index[u]
        path = ls_a.cycle_paths[c]
        i = start
        while True:
            i = (i + 1) % len(path)
            if len(ls_a.vertices[path[i]]) == 2 or i == start:
                break
        return path[i]

    ls = layer_states[layer]
    ls_a = layer_states[layer - 1]
    v_tree = ls.v_by_tree[tree]

    rs.tree_has_merged[layer][tree] = True
    # Refer to the super vertex that tree is part of as super_v
    super_v = rs.tree_to_super_out[layer][tree]

    # Refer to the cycle enclosing tree as outer cycle
    outer_cycle = ls.vertex_to_cycle_above[next(iter(v_tree))]
    # If the outer cycle has no incident trees left uncollapsed, merge_cycle(the outer cycle, super_v) and then return.
    if layer != 1 and len(rs.collapsed_by_cycle[layer - 1]
                          [outer_cycle]) == len(ls_a.cycle_paths[outer_cycle]):
        # We have collapsed every vertex on this cycle, so the cycle as a whole is ready to be merged
        merge_cycle(layer_states, layer - 1, rs, outer_cycle, super_v)
        return
    # Otherwise, if the outer cycle has a single incident tree left uncollapsed, prep_incident_tree(the outer cycle, super_v) and then return.
    elif layer != 1 and len(rs.collapsed_by_cycle[layer - 1][outer_cycle]
                            ) == len(ls_a.cycle_paths[outer_cycle]) - 1:
        # There is a single vertex left uncollapsed, so there must be an incident tree left uncollapsed.
        prep_incident_tree(layer_states, layer - 1, rs, outer_cycle, super_v)
        return
    # Find a vertex adjacent to tree on the outer cycle that, is part of a tree on the same layer as tree and is not in the same super vertex as tree. Refer to that vertex as successor vertex.
    succesor_vertex = tree_successor(layer_states, layer, rs, tree, super_v)

    # If that vertex does not exist, there is nothing to do until the outer cycle is ready to merge because outer cycle is waiting on a tree that is not adjacent to this tree. Return in order to wait for that tree.
    if succesor_vertex == -1:
        # There is no successor for this tree and we are done on this cycle,
        # however, the cycle may not be ready for collapse. So we pass on doing anything.
        return

    # Refer to the tree that the successor vertex is part of as successor_tree.
    succesor_tree = ls.vertex_to_tree[succesor_vertex]
    next_t = ls.vertex_to_tree[succesor_vertex]

    # Because succesor_tree and next_t are now the same super vertex, the predecessor of our successor
    # is our true predecessor now.
    true_pred = ls.vertex_to_sibling_predecessor[succesor_vertex]
    true_succ = ls.nonconsec_to_successor[true_pred]
    succ_tree = ls.vertex_to_tree[true_succ]
    if succ_tree in rs.tree_has_merged[layer]:
        ls.tree_to_nonconsec[next_t].remove(true_pred)

    # If the successor tree is Type-B (we must check its status dynamically)
    if len(ls.supports[succesor_tree]) != 0 and succesor_vertex in rs.collapsed:
        # If the successor tree has merged,there is nothing to do because there is nowhere for us to merge that has not already merged. Just return as the job of this tree is done.
        if succesor_tree in rs.tree_has_merged[layer]:
            # The tree ahead of us has already merged, so there is nowhere else for us to merge into.
            return
        # The successor vertex will never be the root vertex of the successor tree.
        # Otherwise, we merge our super_v into theirs, and then wait for them to merge.
        u = assert_get(ls.supports[succesor_tree])
        # merge super_v and the super vertex of which the successor vertex is a part
        rs.merge_vertex_to_super_out(u, super_v)
    # Otherwise, if the successor tree is Type-B or it has not collapsed yet,merge super and the successor vertex.
    elif len(ls.supports[succesor_tree]
             ) != 0 or not succesor_tree in rs.tree_to_super_out[layer]:
        # This is a tree that has yet to collapse, so just push our super_v into
        # the super and wait for them to collapse.
        rs.merge_to_super_in(succesor_vertex, super_v)

        # The tree that we just merged into may be ready to collapsed
        if len(ls.tree_to_nonconsec[next_t]
               ) > 1 or next_t in rs.tree_will_collapse[layer]:
            # if it is not, or it has already been marked as ready, do nothing
            return

        # If successor tree is ready to collapse, add the successor tree to the queue for this layer so it merges with the proper type.
        rs.tree_will_collapse[layer].add(next_t)
        # The tree we merged into is ready to collapse, so add it to the queue depending on its type
        # The successor tree may be either type A or type B.
        if len(ls.supports[next_t]) == 0:
            rs.operations[layer].append((Ops.COLLAPSE_TYPE_A, next_t))
        elif len(ls.supports[next_t]) == 1:
            rs.operations[layer].append((Ops.COLLAPSE_TYPE_B, next_t))
    # Otherwise, the successor tree is a type A tree that has collapsed but not yet merged.
    elif not succesor_tree in rs.tree_has_merged[layer]:
        # Merge super and the super vertex of which the successor tree is a part
        new_super = rs.circle_plus(rs.tree_to_super_out[layer][succesor_tree],
                                   super_v)
        rs.tree_to_super_out[layer][succesor_tree] = new_super


def merge_type_b(layer_states, layer, rs, v):
    def succ(a):
        x, index = ls.vertex_to_cycle_index[a]
        path = ls.cycle_paths[x]
        return path[(index + 1) % len(path)]

    def pred(a):
        x, index = ls.vertex_to_cycle_index[a]
        path = ls.cycle_paths[x]
        return path[(index - 1) % len(path)]

    ls = layer_states[layer]
    # Refer to the super vertex that v is part of as the super_v
    super_v = rs.vertex_to_super_out[v]
    # Refer to the cycle v is a on as cycle
    cycle = ls.vertex_to_cycle[v]
    # Refer to the tree v is part of as tree
    tree = ls.vertex_to_tree[v]

    # Mark v as collapsed as it was not marked as collapsed earlier.
    rs.collapsed.add(v)
    # Update the data structures keep track of merged trees.
    if not cycle in rs.collapsed_by_cycle[layer]:
        rs.collapsed_by_cycle[layer][cycle] = set()
    rs.collapsed_by_cycle[layer][cycle].add(v)
    ls.trees_by_cycle[cycle].remove(tree)
    rs.tree_has_merged[layer][tree] = True
    # Refer to the clockwise successor of v on cycle as successor_vertex
    succesor_vertex = succ(v)

    # If the successor vertex is an outer vertex
    if len(ls.vertices[succesor_vertex]) == 3:
        # Refer to the tree that the successor vertex is part of as the successor_tree.
        succesor_tree = ls.vertex_to_tree[succesor_vertex]
        # If successor vertex is not part of a super vertex
        if not succesor_tree in rs.tree_has_collapsed[layer] or succesor_tree in rs.tree_has_merged:
            # Merge the super and successor_vertex
            rs.merge_to_super_in(succesor_vertex, super_v)
            # In this case, the vertex has not been collapsed, so merge into it.
            rs.vertex_to_target[v] = succesor_vertex
            # Check if we are about to about to collapse a cycle that has already been added to the queue, or will be very shortly.
            if len(rs.collapsed_by_cycle[layer][cycle]) + 1 != len(
                    ls.cycle_paths[cycle]):
                return

            # If the successor tree is the only tree left on cycle uncollapsed and it is ready to collapse, add the successor tree to the queue for this layer so it merges as a type B tree.
            rs.collapsed_by_cycle[layer][cycle].add(succesor_vertex)
            ls.supports[succesor_tree].remove(succesor_vertex)

            if len(ls.supports[succesor_tree]
                   ) == 1 and len(ls.tree_to_nonconsec[succesor_tree]) <= 1:
                rs.operations[layer].append((Ops.COLLAPSE_TYPE_B,
                                             succesor_tree))
            return

        # Otherwise, if there are any trees on cycle left uncollapsed
        elif len(rs.collapsed_by_cycle[layer][cycle]) != len(
                ls.cycle_paths[cycle]):
            # If we have not collapsed every vertex on this cycle, we push our super_v to the next vertex
            # Merge super and the super node of which the successor_vertex is a part
            rs.merge_vertex_to_super_out(succesor_vertex, super_v)
            return
        else:
            # Otherwise, this entire cycle has been collapsed and is ready to merge.
            # merge_cycle(layer_states, layer, rs, c, super)
            merge_cycle(layer_states, layer, rs, cycle, super_v)
            return
    else:
        assert len(ls.vertices[succesor_vertex]) == 2

        # Merge super and successor_vertex
        rs.merge_to_super_in(succesor_vertex, super_v)
        cycle = ls.vertex_to_cycle[succesor_vertex]
        if len(ls.trees_by_cycle[cycle]) > 1:
            return
        # Though technically we can recurse because there is either 0 or 1 trees left unmerged.
        # It is possible that we have a single tree that is about to merge, so if it is, just wait
        # until it does is.
        if len(ls.trees_by_cycle[cycle]) == 1:
            tree = next(iter(ls.trees_by_cycle[cycle]))
            # The tree is about to merge anyway because its other cycle vertices have collapsed.
            if len(ls.supports[tree]) == 1 and next(
                    iter(ls.supports[tree])) in rs.vertex_to_super_out:
                return
        # If cycle has 0 or 1 incident trees left uncollapsed and it has not been prepared, then prep_cycle(cycle).
        prep_cycle(layer_states, layer, rs, cycle)


def collapse_tree(vertices, x, v_tree, rs):
    # x will always be leaf vertex of tree
    def deg(index):
        return len([a for a in vertices[index] if a in v_tree])

    def index_vertex(v):
        indx[v] = i
        return i + 1

    def set_super(v, new_super):
        vertex_to_super_out[v] = new_super

    def super_in_to_out(v):
        new_super = rs.super_in[v]
        if new_super == frozenset([v]):
            new_super = rs.super_append(new_super)
        vertex_to_super_out[v] = new_super

    def angle_from_twelve(x, y):
        return (pi / 2 - atan2(y, x) + 2 * pi) % (2 * pi)

    def angle_delta(from_pos, to_pos):
        # Our coordinate system has the bottom left as (0,height), so flip the y here
        return angle_from_twelve(to_pos[0] - from_pos[0],
                                 from_pos[1] - to_pos[1])

    def make_angle_above(base, angle):
        if angle < base:
            return 2 * pi + angle
        else:
            return angle

    def pick_angle_by_function(v, fun):
        b = pred[v]
        last_angle = angle_delta(vertices[v].pos, vertices[b].pos)
        possible = [a for a in vertices[v] if a != b and a in v_tree]
        angles_to = [
            angle_delta(vertices[v].pos, vertices[a].pos) for a in possible
        ]
        corrected_angles = [
            make_angle_above(last_angle, angle) for angle in angles_to
        ]
        chosen = possible[corrected_angles.index(fun(corrected_angles))]
        return chosen

    def left_child(v):
        return pick_angle_by_function(v, max)

    def right_child(v):
        return pick_angle_by_function(v, min)

    indx = dict()
    
    vertex_to_super_out = dict()
    for v in vertices:
        vertex_to_super_out[v] = 0

    pred = dict()
    # Refer to the vertex adjacent to x as v
    v = assert_get([a for a in vertices[x] if a in v_tree])
    pred[v] = x
    i = 1

    # If v is a leaf vertex of tree, tree is a tree consisting of two vertices.
    if deg(v) == 1:
        # Assign an index to x
        i = index_vertex(x)
        # Assign an index to v
        i = index_vertex(v)
        super_in_to_out(x)
        super_in_to_out(v)
        # Return the super vertex of x and v
        set_super(x, rs.circle_plus(vertex_to_super_out[x], vertex_to_super_out[v]))
        rs.update_indx(indx)
        return vertex_to_super_out[x]

    while v != x:
        # If v is a leaf vertex, we have reached a leaf node, so it will be indexed and then we will retract.
        if deg(v) == 1:
            super_in_to_out(v)
            # Assign an index to v
            i = index_vertex(v)
            # Set v to the predecessor of v
            v = pred[v]
            continue

        # Refer to the left child of v as l
        l = left_child(v)
        # Refer to the right child of v as l
        r = right_child(v)

        # Both left and right trees must be visited before we can continue
        # If l does not have an index
        if not l in indx:
            # Set the predecessor of l to v
            pred[l] = v
            # set v to l
            v = l
            continue

        # If r does not have an index
        if not r in indx:
            # Set the predecessor of r to v
            pred[r] = v
            # set v to r
            v = r
            continue

        # Note that at this point, l and r may be super vertices, but v is definitely not.
        # As a result, v is ready to collapse.
        super_in_to_out(v)
        # Collapse l and v into a super vertex
        Balpha = rs.circle_plus(vertex_to_super_out[v], vertex_to_super_out[l])
        # Collapse the result with r and store it under v
        set_super(v, rs.circle_plus(Balpha, vertex_to_super_out[r]))
        # Assign an index to v
        i = index_vertex(v)
        # Refer to the predecessor of v as v
        v = pred[v]

    # v == x, so we just merge our traversal with our start
    # Assign an index to x
    i = index_vertex(x)
    v = assert_get([a for a in vertices[x] if a in v_tree])
    super_in_to_out(x)
    rs.update_indx(indx)
    # Collapse x and v into a final super vertex
    set_super(x, rs.circle_plus(vertex_to_super_out[x], vertex_to_super_out[v]))
    # Return that final super vertex
    return vertex_to_super_out[x]
