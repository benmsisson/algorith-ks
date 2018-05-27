from copy import deepcopy

class LayerState:
    def __init__(self, vertices, cycles, cycle_verts, trees, supports, paths,
                 vertex_to_cycle_above):
        self.vertices = vertices

        self.cycles = cycles
        self.cycle_verts = cycle_verts
        self.vertex_to_cycle = dict()
        for i, cycle in enumerate(cycles):
            for u, v in cycle:
                self.vertex_to_cycle[u] = i
                self.vertex_to_cycle[v] = i

        # Note that cycle_paths it is the cycle equivalent of v_by_tree, but it is an ordered list representing
        # a clockwise traversal of the cycle, unlike v_by_tree, which is just a set.
        self.cycle_paths = [[] for _ in cycles]
        marked = set()
        for path in paths:
            for v in path:
                if v in marked or not v in cycle_verts:
                    continue
                marked.add(v)
                self.cycle_paths[self.vertex_to_cycle[v]].append(v)

        self.vertex_to_cycle_index = dict()
        for c, path in enumerate(self.cycle_paths):
            for i, v in enumerate(path):
                self.vertex_to_cycle_index[v] = (c, i)

        self.trees = trees
        self.supports = supports
        self.support_originals = deepcopy(supports)
        self.support_count_original = dict()
        for t in range(len(self.trees)):
            self.support_count_original[t] = len(supports[t])

        self.tree_cycle_to_support_vertex = dict()
        for t, support in enumerate(self.supports):
            for v in support:
                self.tree_cycle_to_support_vertex[(
                    t, self.vertex_to_cycle[v])] = v

        self.v_by_tree = []

        for i, tree in enumerate(trees):
            v_tree = set()
            for u, v in tree:
                v_tree.add(u)
                v_tree.add(v)
            self.v_by_tree.append(v_tree)

        self.paths = paths

        self.vertex_to_path_index = dict()
        for i, path in enumerate(paths):
            for j, v in enumerate(path):
                if len(self.vertices[v]) == 2:
                    self.vertex_to_path_index[v] = (i, j)

        self.vertex_to_tree = dict()
        for i, v_tree in enumerate(self.v_by_tree):
            for v in v_tree:
                self.vertex_to_tree[v] = i

        self.trees_by_cycle = [set() for _ in self.cycles]
        for c, v_cycle in enumerate(self.cycle_paths):
            for v in v_cycle:
                if not v in self.vertex_to_tree:
                    continue
                self.trees_by_cycle[c].add(self.vertex_to_tree[v])

        self.final_support_vertex = dict()

        # Note that vertex_to_cycle_above != vertex_to_cycle for the layer above this one
        # Whereas only vertices on a particular cycle are included in vertex_to_cycle for the layer above
        # Every vertex on this layer is in vertex_to_cycle_above, as every vertex is within a cycle
        # except for the outermost cycle vertices, but then they are themselves contained in a cycle
        # However, a leaf vertex that is a degree 1 vertex on this layer appears in both veretex_to_cycle_above
        # and vertex_to_cycle for the layer above this one, and the cycle as the dictionary value is the same
        self.vertex_to_cycle_above = vertex_to_cycle_above

    def set_path_above(self, ls_a):
        # Like trees_by_cycle, but counting trees with inward vertices instead of outward vertices
        # Note that trees_by_cycle for the layer above != trees_by_cycle_above for this layer
        self.trees_by_cycle_above = [set() for _ in ls_a.cycles]
        self.tree_to_cycle_above = dict()
        for t in range(len(self.trees)):
            for v in self.v_by_tree[t]:
                if v in ls_a.vertex_to_cycle:
                    c = ls_a.vertex_to_cycle[v]
                    self.trees_by_cycle_above[c].add(t)
                    self.tree_to_cycle_above[t] = c
                    break

        # Now that we know the trees that are enclosed within the cycles on the layer above,
        # it is time to reorder the cycles such that the first element in each path is the
        # first vertex (clockwise) of the first tree
        for c, path in enumerate(ls_a.cycle_paths):
            start_tree = -1
            for v in [path[0]] + path[:0:-1]:
                if not v in self.vertex_to_tree:
                    continue
                t = self.vertex_to_tree[v]
                if start_tree == -1:
                    start_tree = t
                if t != start_tree:
                    break
            _, i = ls_a.vertex_to_cycle_index[v]
            i = (i + 1) % len(path)
            path = path[i:] + path[:i]
            ls_a.cycle_paths[c] = path

        # As a result, we must reuse vertex_to_cycle_index
        ls_a.vertex_to_cycle_index = dict()
        for c, path in enumerate(ls_a.cycle_paths):
            for i, v in enumerate(path):
                ls_a.vertex_to_cycle_index[v] = (c, i)

        self.tree_to_nonconsec = dict()
        self.nonconsec_to_successor = dict()
        for t in range(len(self.trees)):
            self.tree_to_nonconsec[t] = set()

        for path in ls_a.cycle_paths:
            path = [path[-1]] + path
            for i, v in enumerate(path[:-1]):
                offset = 1
                index = (i + offset) % len(path)
                u = path[index]
                if not v in self.vertex_to_tree:
                    continue
                while not u in self.vertex_to_tree:
                    offset += 1
                    index = (i + offset) % len(path)
                    u = path[index]
                t = self.vertex_to_tree[v]
                if self.vertex_to_tree[u] != t:
                    self.tree_to_nonconsec[t].add(v)
                    self.nonconsec_to_successor[v] = u

        last_vertex_from_tree = dict()
        self.vertex_to_sibling_predecessor = dict()
        for path in ls_a.cycle_paths:
            # We must make 2 full loops so that the first vertex of every tree gets its predecessor
            # set correctly.
            path = path * 2
            for v in path:
                if not v in self.vertex_to_tree:
                    continue
                t = self.vertex_to_tree[v]
                if not t in last_vertex_from_tree:
                    last_vertex_from_tree[t] = v
                    continue

                self.vertex_to_sibling_predecessor[v] = last_vertex_from_tree[
                    t]
                last_vertex_from_tree[t] = v