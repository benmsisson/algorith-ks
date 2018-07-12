from test import test_all, run_test, run_file
from sys import argv

def handle_argument(argument):
    if argument == "-all":
        test_all()
    elif argument == "-example":
        if len(argv) != 3:
            print("-example takes as input the name of the example to run. Please run with 'python main.py -example NAME_OF_EXAMPLE.graph'")
            return
        run_test(argv[2])
    elif argument == "-file":
        if len(argv) != 3:
            print("-file takes as input the name of the example to run. Please run with 'python main.py -file PATH/TO/FILE.graph'")
            return
        run_file(argv[2])
    else:
        print("Unrecognized command.")

if len(argv) == 1:
    print("Did not receive a commandline argument. Running all tests by default.")
    test_all()
handle_argument(argv[1])
