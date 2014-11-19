#include <string>
#include <iostream>
#include <fstream>
#include <pstream.h>
#include <boost/graph/adjacency_matrix.hpp>
#include <boost/graph/graphviz.hpp>

typedef boost::adjacency_matrix<boost::directedS> digraph_t;
typedef boost::adjacency_matrix<boost::undirectedS> graph_t;

template<class T>
digraph_t readgraph(T & inputfile)
{
    int n, e;

    inputfile >> n;
    inputfile >> e;

    digraph_t result(n);

    for(int i = 0; i < e; i++)
    {
        int v1, v2;

        inputfile >> v1;
        inputfile >> v2;
        boost::add_edge(v1, v2, result);
    }

    inputfile.get();

    return result;
}

bool istransitive(digraph_t & g)
{
    auto vit = boost::vertices(g);

    for(digraph_t::vertex_iterator v = vit.first; v != vit.second; v++)
    {
        auto eit = boost::out_edges(*v, g);

        for(digraph_t::out_edge_iterator e = eit.first; e != eit.second; e++)
        {
            auto eit2 = boost::out_edges(boost::target(*e, g), g);

            for(digraph_t::out_edge_iterator e2 = eit2.first; e2 != eit2.second; e2++)
            {
                if(!boost::edge(*v, boost::target(*e2, g), g).second)
                {
                    return false;
                }
            }
        }
    }

    return true;
}

bool searchorientations(std::string & g6graph)
{
    bool result = false;
    redi::pstream directg(NAUTY_PATH "/directg -Toq");
    directg << g6graph << std::endl;
    redi::peof(directg);

    while(directg.out().peek() != EOF)
    {
        digraph_t candidate = readgraph(directg.out());

        if(istransitive(candidate))
        {
            result = true;
            break;
        }
    }

    directg.close();

    return result;
}

graph_t incomparabilitymatrix(digraph_t & g)
{
    graph_t result(boost::num_vertices(g));
    auto vit = boost::vertices(g);

    for(digraph_t::vertex_iterator v1 = vit.first; v1 != vit.second; v1++)
    {
        for(digraph_t::vertex_iterator v2 = (v1 + 1); v2 != vit.second; v2++)
        {
            if(!boost::edge(*v1, *v2, g).second && !boost::edge(*v2, *v1, g).second)
            {
                boost::add_edge(*v1, *v2, result);
            }
        }
    }

    return result;
}

int main(int argc, char **argv)
{
    for(int i = 1; i < argc; i++)
    {
        std::ifstream inputfile(argv[i]);

        while(inputfile.peek() != EOF)
        {
            digraph_t g = readgraph(inputfile);

            if(istransitive(g))
            {
                auto incmat = incomparabilitymatrix(g);
                auto vit = boost::vertices(incmat);
                std::string g6graph;
                redi::pstream g6converter(NAUTY_PATH "/dretog -q");

                // Print in dreadnaut format
                g6converter  << "n=" << boost::num_vertices(incmat) << " $=0 g" << std::endl;

                for(graph_t::vertex_iterator v1 = vit.first; v1 != vit.second; v1++)
                {
                    g6converter << *v1 << " : ";

                    for(graph_t::vertex_iterator v2 = vit.first; v2 != vit.second; v2++)
                    {
                        if(boost::edge(*v1, *v2, incmat).second)
                        {
                            g6converter << *v2 << ' ';
                        }
                    }

                    g6converter << ";" << std::endl;
                }

                g6converter << "$$" << std::endl;
                redi::peof(g6converter);
                g6converter >> g6graph;
                g6converter.close();

                if(!searchorientations(g6graph))
                {
                    boost::write_graphviz(std::cout, g);
                }
            }
        }
    }

    return 0;
}
