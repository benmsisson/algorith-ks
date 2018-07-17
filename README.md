# algorithm-ks
Implementation of the KS Algorithm for graph reassembling as described in *Efficient Reassembling of Three-Regular Planar Graphs*

[Read the paper on arXiv](https://arxiv.org/abs/1807.03479)

# Instructions
To execute all the tests for KS Algorithm, run the following from your commandline application of choice:
```
python main.py -all
```
To execute a specific prepared example, run:
```
python main.py -example EXAMPLE_NAME.graph
```
Execution steps for examples:
1. First, the name of the graph is printed to the console.
2. The full graph will be displayed. Click on that window to bring up the reassembly GUI. 
4. In the reassembly GUI, the right and left arrow keys move the reassembly process one step forward at a time.

A full list of canned examples is available under the `test_cases\` directory.

To create a graph of your own, run:
```
python graph_builder.py
```
Beware though, as the graph_builder program is not fully tested. It is a good idea to save often when using it.

Once you create your own graph, you can run it using:
```
python main.py -file PATH/TO/FILE.graph
```
