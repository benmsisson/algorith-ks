from enum import Enum, unique
from copy import deepcopy
from collections import deque
from math import pi, atan2
from util.graph_spec import upper_left_most

@unique
class Ops(Enum):
    COLLAPSE_TYPE_A = 0
    COLLAPSE_TYPE_BC = 1
    MERGE_TYPE_A = 2
    MERGE_TYPE_BC = 3

# The basic premise for the algorithm is to start on the outside and move inwards, first collapsing
# Type A trees and Type B trees (with singleton support sets) that have all their vertices in a row,
# and then merging these trees clockwise. This results in more trees that are now ready to be collapsed.
# Though it works outside in, the deeper the trees and cycles, the higher their priority in the queue
# their priority, because they are more recent and because cycles may be waiting for them to collapse before
# the cycle as a whole can merge.
def algorithmKS(layer_states, rs, planarity, check_valid):
    if planarity == 1:
        # Not equipped to handle planarity == 1
        assert False

    prep_cycle(layer_states, 0, rs, 0)

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
            elif op == Ops.COLLAPSE_TYPE_BC:
                collapse_type_bc(layer_states, layer, rs, arg)
            elif op == Ops.MERGE_TYPE_A:
                merge_type_a(layer_states, layer, rs, arg)
            elif op == Ops.MERGE_TYPE_BC:
                merge_type_bc(layer_states, layer, rs, arg)
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


def tree_successor(layer_states, layer, rs, tree, Bout):
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


# prep_cycle is the most complex function in the entire algorith. For a particular cycle, it
# adds every Type A and Type B tree to operations that is ready to be immediately collapsed. However,
# the order in which these trees are collapsed is crucial. If there are any Type A trees at a particular layer
# the first tree to be collapsed MUST be a Type A tree, otherwise, the last cycle could be merged into
# a Type A tree (which would add significantly more complexity to the merging process). Generally, less
# complex structures—like Type A, Type B (singleton support set) trees—are merged into more complex
# structures—like Type C trees and cycles. Though it is usually not linear time to handle merging of
# trees, by being careful with the order, such that every tree (except for one) on a particular cycle is
# collapsed and merged before the next cycle is handled, a lot less information needs to be juggled
# and the complexity is reduced.
def prep_cycle(layer_states, layer, rs, cycle):
    layer = layer + 1
    # Though cycle is on layer, every tree that we wish to prepare for operation is actually on layer + 1
    # so we adjust our frame of reference one layer deeper in order to make things easier to understand.
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

    # Go counterclockwise from the first vertex until we find a different tree than the one we started on.
    # That way, when we go clockwise from that point we can be sure every tree has all of its vertices
    # in a row when it is collapsed.
    # CONDITION C.2

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
    # We find the next tree that has support set > 1 or a support set 1 and a different support cycle
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

    # Now we can find a cycle that has all of its Type B single support trees in a row and start
    # the path at the first Type B tree
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

    # Finally, if it is possible to start at a Type A tree without crossing to another cycle we do so.
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
    # However, if there is a predecessor to a particular tree A with respect to tree B single support
    # cycle, we will collapse that tree, even if A is clockwise after B with respect to cycle.
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
            rs.operations[layer].append((Ops.COLLAPSE_TYPE_BC, t))


# merge cycle is called when we have no incident trees on this cycle that have not been collapsed.
# So we find a tree incident to this cycle that has a successor that has not merged yet
# then merge into that. If there is no such tree, then we esclated this Bout to the cycle above us
def merge_cycle(layer_states, layer, rs, c, Bout):
    ls = layer_states[layer]
    ls_a = layer_states[layer - 1]
    found = False
    next_t = None

    for v in ls.cycle_paths[c]:
        if not v in ls.vertex_to_tree:
            continue
        t = ls.vertex_to_tree[v]
        u = tree_successor(layer_states, layer, rs, t, Bout)
        if not u in ls.vertex_to_tree:
            continue
        next_t = ls.vertex_to_tree[u]
        if next_t in rs.tree_has_merged[layer]:
            continue

        found = True
        break

    if found:
        s = len(ls.supports[next_t])
        # Type A trees all should have been collapsed and merged on a particular cycle before the
        # first cycle is ready to merge.
        assert s != 0
        if s == 1:
            u = next(iter(ls.supports[next_t]))
            rs.merge_into_v_to_Bout(u, Bout)
        else:
            # Should not be merging into such a tree (But if we are then maybe we can just push into the Bin)
            assert False
        return

    # We have completed this layer and this is the final layer, so we have completed the graph!
    if layer == 1:
        return

    # Otherwise, we escalate, and check if we left a tree incident
    # If not then it it time for merge_tree again
    v = ls.cycle_paths[c][0]
    c = ls.vertex_to_cycle_above[v]
    if len(ls_a.trees_by_cycle[c]) != 0:
        prep_incident_tree(layer_states, layer - 1, rs, c, Bout)
    else:
        merge_cycle(layer_states, layer - 1, rs, c, Bout)


def prep_incident_tree(layer_states, layer, rs, c, Bout):
    ls = layer_states[layer]
    t = assert_get(ls.trees_by_cycle[c])
    v = ls.tree_cycle_to_support_vertex[(t, c)]
    # We now have the support vertex on this cycle of the last incident tree,
    # and the Bout that should merge into it, so we do that now.
    rs.merge_into_Bin(v, Bout)
    ls.supports[t].remove(v)
    if len(ls.supports[t]) != 1:
        return
    if t in rs.tree_will_collapse[layer]:
        return
    if len(ls.tree_to_nonconsec[t]) > 1:
        return
    rs.tree_will_collapse[layer].add(t)
    rs.operations[layer].append((Ops.COLLAPSE_TYPE_BC, t))


def collapse_type_a(layer_states, layer, rs, tree):
    # The collapsing of the tree is handled by collapse_tree, however a lot of data structures
    # are keeping track of both the trees and individual vertices that have been collapsed
    # so we update those here.
    ls = layer_states[layer]
    v_tree = ls.v_by_tree[tree]
    start = upper_left_most(ls.vertices, v_tree)
    Bout = collapse_tree(ls.vertices, start, v_tree, rs)
    rs.tree_has_collapsed[layer][tree] = True

    rs.tree_to_Bout[layer][tree] = Bout
    ls_a = layer_states[layer - 1]
    v = next(iter(v_tree))
    c = ls.vertex_to_cycle_above[v]
    for v in v_tree:
        rs.collapsed.add(v)
        # If we are not at least at layer 2 depth, we are not within a cycle that can contain an incident tree
        if layer < 2 or len(ls.vertices[v]) != 1:
            continue

        rs.collapsed_by_cycle[layer - 1][c].add(v)

    rs.operations[layer].append((Ops.MERGE_TYPE_A, tree))

def collapse_type_bc(layer_states, layer, rs, tree):
    ls = layer_states[layer]
    if len(ls.supports[tree]) == 0:
        # Because all supports of this Type BC tree were collapsed at the same time,
        # we can handle it as a Type A, which we will do immmediately to preserve order.
        collapse_type_a(layer_states,layer,rs,tree)
        return
    v_tree = ls.v_by_tree[tree]
    v = assert_get(ls.supports[tree])
    Bout = collapse_tree(ls.vertices, v, v_tree, rs)
    rs.tree_has_collapsed[layer][tree] = True

    for u in v_tree:
        if u != v:
            # We will add the support vertex to collapsed when we merge this tree
            rs.collapsed.add(u)

    c = ls.vertex_to_cycle[v]
    rs.vertex_to_Bout[v] = Bout
    rs.operations[layer].append((Ops.MERGE_TYPE_BC, v))


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
    Bout = rs.tree_to_Bout[layer][tree]

    c = ls.vertex_to_cycle_above[next(iter(v_tree))]
    if layer != 1 and len(rs.collapsed_by_cycle[layer - 1][c]) == len(
            ls_a.cycle_paths[c]):
        # We have collapsed every vertex on this cycle, so the cycle as a whole is ready to be merged
        merge_cycle(layer_states, layer - 1, rs, c, Bout)

        return
    elif layer != 1 and len(rs.collapsed_by_cycle[layer - 1]
                            [c]) == len(ls_a.cycle_paths[c]) - 1:
        # There is a single vertex left uncollapsed, so there must be an incident tree left uncollapsed.
        prep_incident_tree(layer_states, layer - 1, rs, c, Bout)
        return
    next_v = tree_successor(layer_states, layer, rs, tree, Bout)
    if next_v == -1:
        # There is no successor for this tree and we are done on this cycle,
        # however, the cycle may not be ready for collapse. So we pass on doing anything.
        return

    t = ls.vertex_to_tree[next_v]
    next_t = ls.vertex_to_tree[next_v]

    # Because t and next_t are now the same super node, the predecessor of our successor
    # is our true predecessor now.
    true_pred = ls.vertex_to_sibling_predecessor[next_v]
    true_succ = ls.nonconsec_to_successor[true_pred]
    succ_tree = ls.vertex_to_tree[true_succ]
    if succ_tree in rs.tree_has_merged[layer]:
        ls.tree_to_nonconsec[next_t].remove(true_pred)

    if len(ls.supports[t]) != 0 and next_v in rs.collapsed:
        if t in rs.tree_has_merged[layer]:
            # The tree ahead of us has already merged, so there is nowhere else for us to merge into.
            return
        # Otherwise, we merge our Bout into theirs, and then wait for them to merge.
        u = assert_get(ls.supports[t])
        rs.merge_into_v_to_Bout(u, Bout)
    # note the or here whereas the above was linked with an and
    elif len(ls.supports[t]) != 0 or not t in rs.tree_to_Bout[layer]:
        # This is a tree that has yet to collapse, so just push our Bout into
        # the Bin and wait for them to collapse.
        rs.merge_into_Bin(next_v, Bout)

        # The tree that we just merged into may be ready to collapsed
        if len(ls.tree_to_nonconsec[next_t]
               ) > 1 or next_t in rs.tree_will_collapse[layer]:
            # if it is not, or it has already been marked as ready, do nothing
            return

        rs.tree_will_collapse[layer].add(next_t)
        # The tree we merged into is ready to collapse, so add it to the queue depending on its type
        if len(ls.supports[next_t]) == 0:
            rs.operations[layer].append((Ops.COLLAPSE_TYPE_A, next_t))
        elif len(ls.supports[next_t]) == 1:
            rs.operations[layer].append((Ops.COLLAPSE_TYPE_BC, next_t))

    elif not t in rs.tree_has_merged[layer]:
        # Ahead of us is a type A tree that has already collapsed but has yet to merge.
        n_Bout = rs.circle_plus(rs.tree_to_Bout[layer][t], Bout)
        rs.tree_to_Bout[layer][t] = n_Bout


def merge_type_bc(layer_states, layer, rs, v):
    def succ(a):
        x, index = ls.vertex_to_cycle_index[a]
        path = ls.cycle_paths[x]
        return path[(index + 1) % len(path)]

    def pred(a):
        x, index = ls.vertex_to_cycle_index[a]
        path = ls.cycle_paths[x]
        return path[(index - 1) % len(path)]

    ls = layer_states[layer]
    Bout = rs.vertex_to_Bout[v]
    c = ls.vertex_to_cycle[v]
    t = ls.vertex_to_tree[v]

    # Update the data structures keep track of merged trees. Note that the support vertex is now
    # finally considered collapsed.
    rs.collapsed.add(v)
    if not c in rs.collapsed_by_cycle[layer]:
        rs.collapsed_by_cycle[layer][c] = set()
    rs.collapsed_by_cycle[layer][c].add(v)
    ls.trees_by_cycle[c].remove(t)
    rs.tree_has_merged[layer][t] = True
    u = succ(v)

    if len(ls.vertices[u]) == 3:
        next_t = ls.vertex_to_tree[u]
        if not next_t in rs.tree_has_collapsed[layer] or next_t in rs.tree_has_merged:
            # In this case, the vertex has not been collapsed, so merge into it
            # and if the tree now has all of its vertices in a row, it is ready to collapse.
            rs.merge_into_Bin(u, Bout)
            rs.vertex_to_target[v] = u
            if len(rs.collapsed_by_cycle[layer][c]) + 1 != len(
                    ls.cycle_paths[c]):
                return
            rs.collapsed_by_cycle[layer][c].add(u)
            ls.supports[next_t].remove(u)

            if len(ls.supports[next_t]
                   ) == 1 and len(ls.tree_to_nonconsec[next_t]) <= 1:
                rs.operations[layer].append((Ops.COLLAPSE_TYPE_BC, next_t))
            return

        elif len(rs.collapsed_by_cycle[layer][c]) != len(ls.cycle_paths[c]):
            # If we have not collapsed every vertex on this cycle, we push our Bout to the next vertex
            rs.merge_into_v_to_Bout(u, Bout)
            return

        else:
            # Otherwise, this entire cycle has been collapsed and is ready to merge.
            merge_cycle(layer_states, layer, rs, c, Bout)
            return

    else:
        assert len(ls.vertices[u]) == 2

        rs.merge_into_Bin(u, Bout)
        c = ls.vertex_to_cycle[u]
        if len(ls.trees_by_cycle[c]) > 1:
            return
        # Though technically we can recurse because there is either 0 or 1 trees left unmerged.
        # It is possible that we have a single tree that is about to merge, so if it is, just wait
        # until it does is.
        if len(ls.trees_by_cycle[c]) == 1:
            t = next(iter(ls.trees_by_cycle[c]))
            if len(ls.supports[t]) == 1 and next(
                    iter(ls.supports[t])) in rs.vertex_to_Bout:
                return

        prep_cycle(layer_states, layer, rs, c)


def collapse_tree(vertices, x, v_tree, rs):
    def deg(index):
        return len([a for a in vertices[index] if a in v_tree])

    def index_vertex(v):
        indx[v] = i
        return i + 1

    def set_Bout(v, Bval):
        Bout[v] = Bval

    def set_Bout_from_Bin(v):
        Bval = rs.Bin[v]
        if Bval == frozenset([v]):
            Bval = rs.super_append(Bval)
        Bout[v] = Bval

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
    Bout = [0 for _ in vertices]
    pred = dict()
    v = assert_get([a for a in vertices[x] if a in v_tree])
    pred[v] = x
    i = 1

    # This is a tree consisting of two nodes, so we just merge the two and return
    if deg(v) == 1:
        i = index_vertex(x)
        i = index_vertex(v)
        set_Bout_from_Bin(x)
        set_Bout_from_Bin(v)
        set_Bout(x, rs.circle_plus(Bout[x], Bout[v]))
        rs.update_indx(indx)
        return Bout[x]

    while v != x:
        if deg(v) == 1:
            # We have reached a leaf node, so it will be indexed and then we will retract.
            set_Bout_from_Bin(v)
            i = index_vertex(v)
            v = pred[v]
            continue

        l = left_child(v)
        r = right_child(v)

        # Both left and right trees must be visited before we can continue
        if not l in indx:
            pred[l] = v
            v = l
            continue

        if not r in indx:
            pred[r] = v
            v = r
            continue

        # At this point, both l and r are either degree 1 or are already collapsed, so v is ready
        # to merge its branches.
        set_Bout_from_Bin(v)
        Balpha = rs.circle_plus(Bout[v], Bout[l])
        set_Bout(v, rs.circle_plus(Balpha, Bout[r]))
        i = index_vertex(v)
        v = pred[v]

    # v == x, so we just merge our traversal with our start
    i = index_vertex(x)
    v = assert_get([a for a in vertices[x] if a in v_tree])
    set_Bout_from_Bin(x)
    rs.update_indx(indx)
    set_Bout(x, rs.circle_plus(Bout[x], Bout[v]))
    return Bout[x]
