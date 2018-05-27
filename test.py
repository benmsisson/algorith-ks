from util.file_io import read_graph
from algorithm.driver import start_reassembly

def run_test(graph_name):
    file_name = "test_cases/"+graph_name+".graph"
    vertices = read_graph(file_name)
    start_reassembly(vertices,graph_name)

# Some  test cases, roughly in increasing order of complexity.

# Planarity 2
run_test("dual_tree")

run_test("pentagon_tree")

run_test("tree_pair")

run_test("example_1")

run_test("nested_tree")

run_test("many_trees")

run_test("square_center")

run_test("paired_nested_tree")

run_test("example_3")

run_test("example_3_extended")
    
# Planarity 3
run_test("triple_square")

run_test("five_squares")

run_test("semi_square_triple")

run_test("rotating_squares")

# Planarity 4
run_test("example_2")

run_test("nested_squares")

run_test("nested_diamond")

run_test("squared_diamonds")

run_test("optimal")
