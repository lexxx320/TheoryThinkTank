#include <string>
#include <iostream>
#include <ctime>
#include <cstdlib>
#include <queue>
#include <cassert>

#include <boost/program_options.hpp>
#include <boost/format.hpp>
#include <boost/optional.hpp>
#include <boost/algorithm/string.hpp>
#include <boost/graph/adjacency_matrix.hpp>
#include <boost/graph/isomorphism.hpp>
#include <boost/graph/topological_sort.hpp>
#include <boost/graph/graphviz.hpp>

typedef boost::adjacency_matrix<boost::directedS, boost::property<boost::vertex_name_t, std::string>> digraph_t;
typedef std::vector<digraph_t::vertex_descriptor> path;

digraph_t inducedgraph(const digraph_t & v1, const digraph_t & v2)
{
    digraph_t result(boost::num_vertices(v1));

    assert(boost::num_vertices(v1) == boost::num_vertices(v2));

    // Transfer names
    for(size_t i = 0; i < boost::num_vertices(v1); i++)
    {
        boost::put(boost::vertex_name, result, i, boost::get(boost::vertex_name, v1, i));
    }

    for(size_t i = 0; i < boost::num_vertices(v1); i++)
    {
        for(size_t j = i + 1; j < boost::num_vertices(v1); j++)
        {
            int score = 0;

            if(boost::edge(i, j, v1).second)
            {
                score++;
            }

            if(boost::edge(i, j, v2).second)
            {
                score++;
            }

            if(boost::edge(j, i, v1).second)
            {
                score--;
            }

            if(boost::edge(j, i, v2).second)
            {
                score--;
            }

            if(score > 0)
            {
                boost::add_edge(i, j, result);
            }

            if(score < 0)
            {
                boost::add_edge(j, i , result);
            }
        }
    }

    return result;
}

std::vector<path> getcycles(const digraph_t & g)
{
    std::vector<path> result;
    std::queue<path> pathqueue;
    auto vit = boost::vertices(g);

    for (auto v = vit.first; v != vit.second; v++)
    {
        pathqueue.push( { *v });
    }

    while (!pathqueue.empty())
    {
        const path current_path = pathqueue.front();
        const digraph_t::vertex_descriptor max = current_path.front();
        auto vicinity = boost::out_edges(current_path.back(), g);

        for (auto i = vicinity.first; (i != vicinity.second) && (boost::target(*i, g) <= max); i++)
        {
            auto neighbor = boost::target(*i, g);
            auto prev = std::find(current_path.cbegin(), current_path.cend(), neighbor);

            if (prev == current_path.cend())
            {
                path new_path(current_path);

                new_path.push_back(neighbor);
                pathqueue.push(new_path);
            }
            else
            {
                if (prev == current_path.cbegin())
                {
                    result.push_back(current_path);
                    break;
                }
            }
        }

        pathqueue.pop();
    }

    return result;
}

digraph_t stringtovote(const std::string & votestr)
{
    std::vector<std::string> candidates;
    std::vector<std::string> order;

    boost::split(candidates, votestr, boost::is_any_of(">="));
    boost::split(order, votestr, !boost::is_any_of(">="), boost::token_compress_on);
    assert(order.size() == candidates.size() + 1);

    std::map<std::string, size_t> vertexidx;
    std::vector<std::string> orderedcandidates(candidates);
    auto currentclass = candidates.cbegin();

    std::sort(orderedcandidates.begin(), orderedcandidates.end());

    for(auto c : candidates)
    {
        vertexidx[c] = std::find(orderedcandidates.cbegin(), orderedcandidates.cend(), c) - orderedcandidates.cbegin();
    }

    digraph_t vote(candidates.size());
    auto vit = boost::vertices(vote);

    for(auto v = vit.first; v != vit.second; v++)
    {
        boost::put(boost::vertex_name, vote, *v, orderedcandidates[v - vit.first]);
    }

    for(auto i = candidates.cbegin(); i < candidates.cend(); i++)
    {
        for(auto j = candidates.cbegin(); j < i; j++)
        {
            boost::add_edge(vertexidx[*j], vertexidx[*i], vote);
        }

        for(auto j = currentclass; j < i; j++)
        {
            boost::add_edge(vertexidx[*i], vertexidx[*j], vote);
        }

        if(order[i - candidates.cbegin() + 1] == ">")
        {
            currentclass = i + 1;
        }
    }

    return vote;
}

void applyrules(digraph_t & v, const digraph_t & v1, const digraph_t & v2, size_t i, size_t j, boost::optional<std::pair<size_t, size_t>> & choice)
{
    // Rule 0
    if(boost::edge(i, j, v1).second && !boost::edge(j, i, v1).second)
    {
        boost::add_edge(i, j, v);
    }

    if(boost::edge(i, j, v1).second && boost::edge(j, i, v1).second)
    {
        // Rule 1
        if(boost::edge(i, j, v2).second && !boost::edge(j, i, v2).second)
        {
            boost::add_edge(i, j, v);
        }

        // Rule 2
        if(boost::edge(i, j, v2).second && boost::edge(j, i, v2).second)
        {
            // We do this just once
            if(i < j)
            {
                if(!choice)
                {
                    // We get to pick
                    int coin = rand() % 2;

                    choice = std::make_pair(coin ? i : j, coin ? j : i);
                    boost::add_edge(choice->first, choice->second, v);
                }
                else
                {
                    // Already picked, we choose the opposite
                    boost::add_edge(choice->second, choice->first, v);
                }
            }
        }
    }
}

std::pair<digraph_t, digraph_t> convertvotes(const digraph_t & v1, const digraph_t & v2)
{
    std::vector<std::string> candidates(boost::num_vertices(v1));
    digraph_t tv1(boost::num_vertices(v1));
    digraph_t tv2(boost::num_vertices(v2));

    for(size_t i = 0; i < boost::num_vertices(v1); i++)
    {
        const std::string & vname = boost::get(boost::vertex_name, v1, i);

        boost::put(boost::vertex_name, tv1, i, vname);
        boost::put(boost::vertex_name, tv2, i, vname);

        for(size_t j = 0; j < boost::num_vertices(v1); j++)
        {
            if(i != j)
            {
                boost::optional<std::pair<size_t, size_t>> choice;

                applyrules(tv1, v1, v2, i, j, choice);
                applyrules(tv2, v2, v1, i, j, choice);
            }
        }
    }

    auto tv1cycles = getcycles(tv1);
    auto tv2cycles = getcycles(tv2);

    // I claim these are the same cycles...
    assert(tv1cycles.size() == tv2cycles.size());

    while(!tv1cycles.empty())
    {
        for(size_t i = 0; i < tv1cycles.size(); i++)
        {
            // ... but reversed...
            assert(std::equal(tv1cycles[i].cbegin() + 1, tv1cycles[i].cend(), tv2cycles[i].crbegin()));

            // ... and they all come from Rule 2
            for(auto j = tv1cycles[i].cbegin(); j < tv1cycles[i].cend(); j++)
            {
                auto jsource = *j;
                auto jtarget = ((j + 1) == tv1cycles[i].cend()) ? tv1cycles[i].front() : *(j + 1);

                assert(boost::edge(jsource, jtarget, v1).second);
                assert(boost::edge(jtarget, jsource, v1).second);
                assert(boost::edge(jsource, jtarget, v2).second);
                assert(boost::edge(jtarget, jsource, v2).second);
            }
        }

        auto maxcycle = std::max_element(tv1cycles.cbegin(), tv1cycles.cend(), [](const path & a, const path & b) {
            return a.size() < b.size();
        });

        // I claim I can flip any edge in a cycle of max length
        int flip = rand() % maxcycle->size();
        auto flipsource = maxcycle->at(flip);
        auto fliptarget = ((flip + 1) == maxcycle->size()) ? maxcycle->front() : maxcycle->at(flip + 1);

        boost::remove_edge(flipsource, fliptarget, tv1);
        boost::add_edge(fliptarget, flipsource, tv1);
        boost::remove_edge(fliptarget, flipsource, tv2);
        boost::add_edge(flipsource, fliptarget, tv2);

        tv1cycles = getcycles(tv1);
        tv2cycles = getcycles(tv2);
    }

    return std::make_pair(tv1, tv2);
}

void writeconvertedvotes(const digraph_t & v1, const digraph_t & v2)
{
    std::vector<digraph_t::vertex_descriptor> v1revsorted(boost::num_vertices(v1));
    std::vector<std::string> v1candidates(boost::num_vertices(v1));
    std::vector<digraph_t::vertex_descriptor> v2revsorted(boost::num_vertices(v2));
    std::vector<std::string> v2candidates(boost::num_vertices(v2));

    // This will throw an exception if the graphs are not DAGs
    boost::topological_sort(v1, v1revsorted.begin());
    boost::topological_sort(v2, v2revsorted.begin());

    std::transform(v1revsorted.crbegin(), v1revsorted.crend(), v1candidates.begin(), [v1](const digraph_t::vertex_descriptor v) {
        return boost::get(boost::vertex_name, v1, v);
    });
    std::transform(v2revsorted.crbegin(), v2revsorted.crend(), v2candidates.begin(), [v2](const digraph_t::vertex_descriptor v) {
        return boost::get(boost::vertex_name, v2, v);
    });

    std::cout << boost::join(v1candidates, ">") << std::endl;
    std::cout << boost::join(v2candidates, ">") << std::endl;
}

int main(int argc, char **argv)
{
    boost::program_options::options_description desc("Options");
    boost::program_options::variables_map vm;
    size_t n;
    std::string v1string, v2string;

    desc.add_options()("v1", boost::program_options::value<std::string>(&v1string), "First vote");
    desc.add_options()("v2", boost::program_options::value<std::string>(&v2string), "Second vote");
    desc.add_options()("random,r", boost::program_options::value<size_t>(&n), "Generate two random votes of size n");
    boost::program_options::store(boost::program_options::parse_command_line(argc, argv, desc), vm);
    boost::program_options::notify(vm);

    if(vm.count("random"))
    {
        std::vector<size_t> v2shuffle(n);

        srand(time(NULL));

        for(size_t i = 0; i < n; i++)
        {
            v1string += boost::str(boost::format("a%1%") % i);
            v2shuffle[i] = i;

            if(i < n - 1)
            {
                v1string += (rand() % 2) ? ">" : "=";
            }
        }

        std::random_shuffle(v2shuffle.begin(), v2shuffle.end());

        for(size_t i = 0; i < n; i++)
        {
            v2string += boost::str(boost::format("a%1%") % v2shuffle[i]);

            if(i < n - 1)
            {
                v2string += (rand() % 2) ? ">" : "=";
            }
        }

        std::cout << "--v1 \"" << v1string << "\"" << std::endl;
        std::cout << "--v2 \"" << v2string << "\"" << std::endl;
    }

    digraph_t v1 = stringtovote(v1string);
    digraph_t v2 = stringtovote(v2string);

    // Consistency checks
    assert(boost::num_vertices(v1) ==  boost::num_vertices(v2));

    for(size_t i = 0; i < boost::num_vertices(v1); i++)
    {
        assert(boost::get(boost::vertex_name, v1, i) == boost::get(boost::vertex_name, v2, i));
    }

    digraph_t originalinducedgraph = inducedgraph(v1, v2);
    auto convertedvotes = convertvotes(v1, v2);

    // More consistency checks
    assert(boost::num_edges(convertedvotes.first) == boost::num_edges(convertedvotes.second));
    assert(boost::num_edges(convertedvotes.first) == boost::num_vertices(convertedvotes.first) * (boost::num_vertices(convertedvotes.first) - 1) / 2);

    digraph_t newinducedgraph = inducedgraph(convertedvotes.first, convertedvotes.second);

    // Must be identical
    assert(boost::num_vertices(originalinducedgraph) == boost::num_vertices(newinducedgraph));
    assert(boost::num_edges(originalinducedgraph) == boost::num_edges(newinducedgraph));

    for(size_t i = 0; i < boost::num_vertices(originalinducedgraph); i++)
    {
        auto eit = boost::out_edges(boost::vertex(i, originalinducedgraph), originalinducedgraph);

        assert(boost::get(boost::vertex_name, originalinducedgraph, i) == boost::get(boost::vertex_name, newinducedgraph, i));

        for(auto e = eit.first; e != eit.second; e++)
        {
            size_t j = boost::vertex(boost::target(*e, originalinducedgraph), originalinducedgraph);

            assert(boost::edge(i, j, newinducedgraph).second);
        }
    }

    writeconvertedvotes(convertedvotes.first, convertedvotes.second);

    return 0;
}
