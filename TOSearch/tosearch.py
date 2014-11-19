from pygraph.classes.digraph import digraph
from pygraph.classes.graph import graph

import sys
import os
import subprocess

# Replace with the location of nauty
nautyloc = "path/to/nauty"

def readgraph(line):
    edges = line.strip().split()
    n = int(edges[0])
    e = int(edges[1])
    g = digraph()

    g.add_nodes(range(0, n))

    for i in range(0, e):
        # The first 2 edges were actually
        # the number of nodes and edges
        edge = (int(edges[2 + 2 * i]), int(edges[3 + 2 * i]))
        g.add_edge(edge)
    
    return g    

def readgraphs(inputfile):
    for l in inputfile:
        yield readgraph(l)

def istransitive(g):
    for v1 in g.nodes():
        for v2 in g.neighbors(v1):
            for v3 in g.neighbors(v2):
                if not g.has_edge((v1, v3)):
                    return False

    return True

def incomparabilitygraph(g):
    nodes = g.nodes()
    result = graph()

    result.add_nodes(nodes)

    for v1 in nodes:
        for v2 in nodes:
            if v1 != v2:
                if not (g.has_edge((v1, v2)) or g.has_edge((v2, v1))):
                    if not result.has_edge((v1, v2)):
                        result.add_edge((v1, v2))

    return result

def graph2dre(g):
    result = "n=%s $=0 g\n" % len(g.nodes())

    for n in g.nodes():
        result += "%s: %s;\n" % (n, ",".join(str(x) for x in g.neighbors(n)))

    result += "$$\n"

    return result

def getg6(g):
    dretog = subprocess.Popen([os.path.join(nautyloc, "dretog"), "-q"], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    (dretogout, dretgerr) = dretog.communicate(graph2dre(g))

    return dretogout

def getorientations(g):
    g6 = getg6(g)
    directg = subprocess.Popen([os.path.join(nautyloc, "directg"), "-Toq"], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    (directgout, dretgerr) = directg.communicate(g6)
    graphs = directgout.splitlines()

    for g in graphs:
        yield readgraph(g)
    

if __name__ == "__main__":
    inputfile = open(sys.argv[1], "r")

    for g in readgraphs(inputfile):
        if istransitive(g):
            incompg = incomparabilitygraph(g)
            hasorientation = False

            for orientg in getorientations(incompg):
                if istransitive(orientg):
                    hasorientation = True
                    break

            if not hasorientation:
                print g
