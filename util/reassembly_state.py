from collections import deque
from copy import deepcopy

class ReassemblyState(object):
    def __init__(self, vertices, planarity):
        self.vertices = vertices

        self.Bin = [0] * len(vertices)
        for v in range(len(vertices)):
            self.Bin[v] = frozenset([v])

        self.dir_G = deepcopy(vertices)
        self.collapsed = set()

        self.indx = dict()
        self.total_i = 0
        self.vertex_to_Bout = dict()

        self.operations = []
        self.collapsed_by_cycle = []
        self.tree_has_collapsed = []
        self.tree_has_merged = []
        self.tree_will_collapse = []
        self.tree_to_Bout = []

        self.vertex_to_target = dict()

        for layer in range(planarity):
            self.operations.append(deque())
            self.collapsed_by_cycle.append(dict())
            self.tree_has_collapsed.append(dict())
            self.tree_has_merged.append(dict())
            self.tree_will_collapse.append(set())
            self.tree_to_Bout.append(dict())

        self.re_list = [0] * (2 * len(self.vertices) - 1)
        self.re_index = 0

    def super_append(self, v):
        # Should be a set consisiting of v where v is a vertex
        assert len(v) == 1
        self.re_list[self.re_index] = v
        self.re_index += 1
        return self.re_index - 1

    def circle_plus(self, v, u):
        self.re_list[self.re_index] = (v, u)
        self.re_index += 1
        return self.re_index - 1

    def update_indx(self, indx):
        n_i = self.total_i
        for v, i in indx.items():
            self.indx[v] = i + self.total_i
            n_i += 1
        self.total_i = n_i

    def direct_edge(self, u, v):
        if u in self.dir_G[v]:
            self.dir_G[v].remove_edge(u)

    def merge_into_v_to_Bout(self, v, Bout):
        if v in self.collapsed:
            assert v in self.vertex_to_target
            u = self.vertex_to_target[v]
            if u in self.vertex_to_Bout:
                self.vertex_to_Bout[u] = self.circle_plus(self.vertex_to_Bout[u], Bout)
            else:
                self.Bin[u] = self.circle_plus(self.Bin[u], Bout)
            return
        n_Bout = self.circle_plus(self.vertex_to_Bout[v], Bout)
        self.vertex_to_Bout[v] = n_Bout

    def merge_into_Bin(self, v, Bout):
        Bval = self.super_append(self.Bin[v])
        n_Bout = self.circle_plus(Bval, Bout)
        self.Bin[v] = n_Bout

    def build_Blst(self):
        self.Blst = [0] * len(self.re_list)
        for i, v in enumerate(self.re_list):
            if i >= self.re_index:
                return
            if len(v) == 1:
                self.Blst[i] = v
            else:
                u, v = v
                self.Blst[i] = self.Blst[u].union(self.Blst[v])
