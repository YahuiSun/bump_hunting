// bumphunting.cpp : This file contains the 'main' function. Program execution begins and ends there.

#include "pch.h"
#include <iostream>
#include <iomanip>
#include <fstream>
#include <ctime>
#include <cstdint>
#include <cstdlib>
#include <numeric>
#include <string>
#include <list>
#include <vector>
#include <tuple>
#include <algorithm>
#include <iterator>
#include <chrono>
#include <typeinfo>
#include <unordered_set>
#include <unordered_map>

/*header files in the Boost library: https://www.boost.org/*/
#include <boost/random.hpp>
#include <boost/config.hpp>
#include <boost/graph/connected_components.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/heap/pairing_heap.hpp> // pairing_heap uses less memory
#include <boost/graph/prim_minimum_spanning_tree.hpp>
#include <boost/thread.hpp>
#include <boost/chrono.hpp>
#include <boost/thread/scoped_thread.hpp>


/*header files in the YS-Graph-Library: https://github.com/YahuiSun/YS-Graph-Library*/
#include <subgraph_unordered_map.h> 
#include <boost_graph.h> 
#include <boost_graph_print_vertices_and_edges.h> 
#include <boost_graph_does_this_edge_exist.h> 
#include <boost_graph_breadth_first_search_a_tree_of_edges.h> 
#include <boost_graph_ec_update_pairwise_jaccard_distance.h> 
#include <parse_string.h> 
#include <read_csv.h> 


using namespace std;
using namespace boost::heap;


// definitions

#pragma region
struct node {
	int index;
	double priority_value;
}; // define the node in the queue
bool operator<(node const& x, node const& y) {
	return x.priority_value > y.priority_value; // < is the max-heap; > is the min heap; PriorityQueue is expected to be a max-heap of integer values
} // redefine the operator since there are multiple values in each node
typedef typename pairing_heap<node>::handle_type handle_t; // define the handle type for pairing_heap<node>
#pragma endregion define heaps  

#pragma region
struct node_max_heaps_int_index {
	int index;
	double priority_value;
}; // define the node in the queue
bool operator<(node_max_heaps_int_index const& x, node_max_heaps_int_index const& y) {
	return x.priority_value < y.priority_value; // < is the max-heap; > is the min heap; PriorityQueue is expected to be a max-heap of integer values
} // redefine the operator since there are multiple values in each node
typedef typename pairing_heap<node_max_heaps_int_index>::handle_type handle_max_heaps_int_index; // define the handle type for pairing_heap<node>
#pragma endregion define max_heaps_int_index

#pragma region
struct node_max_heaps_edge_index {
	pair<int, int> index;
	double priority_value;
}; // define the node in the queue
bool operator<(node_max_heaps_edge_index const& x, node_max_heaps_edge_index const& y) {
	return x.priority_value < y.priority_value; // < is the max-heap; > is the min heap; PriorityQueue is expected to be a max-heap of integer values
} // redefine the operator since there are multiple values in each node
typedef typename pairing_heap<node_max_heaps_edge_index>::handle_type handle_max_heaps_edge_index; // define the handle type for pairing_heap<node>
#pragma endregion define max_heaps_edge_index




// some universal codes

#pragma region
vector<pair<vector<int>, vector<pair<int, int>>>> copy_trees(vector<pair<vector<int>, vector<pair<int, int>>>>& tree) {
	return tree;
}
#pragma endregion copy_trees

#pragma region
pair<vector<int>, vector<pair<int, int>>> copy_tree(pair<vector<int>, vector<pair<int, int>>>& tree) {
	return tree;
}
#pragma endregion copy_tree

// algorithms bases

#pragma region
double forest_net_weight(graph& initial_graph, vector<pair<vector<int>, vector<pair<int, int>>>>& trees) {


	int N = num_vertices(initial_graph); 
	double net_weight = 0;

	for (int i = 0; i < trees.size(); i++) { // the ith tree

		for (int j = 0; j < trees[i].first.size(); j++) {
			net_weight = net_weight + get(boost::vertex_name_t(), initial_graph, trees[i].first[j]); // plus included node weights
		}
		for (int j = 0; j < trees[i].second.size(); j++) {
			int v1 = trees[i].second[j].first;
			int v2 = trees[i].second[j].second;
			net_weight = net_weight -
				get(boost::edge_weight_t(), initial_graph, boost::edge(v1, v2, initial_graph).first); // included edge costs
		}
	}

	return net_weight;

}
#pragma endregion forest_net_weight

#pragma region
vector<pair<vector<int>, vector<pair<int, int>>>> FGW_growth_forest(graph& input_graph, double distribution_ratio, int& target_k) {


	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	graph::out_edge_iterator eit, eend;

	
	vector<pair<vector<int>, vector<pair<int, int>>>> solution_trees(target_k); // the solution trees: pair<included_vertices,included_edges>


	double Global_time = 0; // global time
	int Active_C_num = 0; // the number of active clusters

	int N = num_vertices(input_graph); // number of vertices
	int ep_num = num_edges(input_graph) * 2; // total number of edge parts
	int ep_order = 0;
	node node0;

	// Clusters: the number of clusters is always N
	vector<bool> C_activity(N); // activity value of each C; false means inactive; initial value is false
	vector<double> C_event_time(N); // the event time for each C
	vector<vector<int>> C_V_list(N); // record the vertices in each C
	vector<pairing_heap<node>> C_ep_PQ(N); // the PQ for edge parts in each C; node index: ep order in ep_list
	vector<int> V_locator(N); // the index of the maximal cluster containing the vertex

	// edge parts: PQ and their handles
	vector<int> ep_v1_list(ep_num); // class may be slow, so I seperate the ep_list
	vector<int> ep_v2_list(ep_num);
	vector<double> ep_EventTime_list(ep_num);
	vector<int> ep_ep2_order_list(ep_num);
	vector<handle_t> handle_ep(ep_num); // store the handle for each edge part

	// the event PQ and their handles
	pairing_heap<node> C_event_PQ; // PQ storing the event time of the active clusters; node index: cluster order
	vector<handle_t> handle_Cevent(N);
	pairing_heap<node> E_event_PQ; // PQ storing the active clusters; node index: cluster order
	vector<handle_t> handle_Eevent(N);

	

	// initialize the clusters
	for (int i = 0; i < N; i++)
	{
		C_V_list[i].insert(C_V_list[i].end(), i); // insert a vertex into the rear of C_V_list[i]; each vertex is a singular cluster
		V_locator[i] = i; // the maximal cluster containing vertex i


		// add edge parts into C
		boost::tie(ai, a_end) = boost::adjacent_vertices(i, input_graph); // adjacent_vertices of i
		for (; ai != a_end; ai++) {

			int j = *ai;// the adjacent vetex to i
			if (j > i) { // don't overcheck an edge
				// the first ep
				ep_v1_list[ep_order] = i;
				ep_v2_list[ep_order] = j;
				ep_EventTime_list[ep_order] = get(boost::edge_weight_t(), input_graph, boost::edge(i, j, input_graph).first) / distribution_ratio; // halve the edge cost
				ep_ep2_order_list[ep_order] = ep_order + 1; // it points to the ep below
				node0.index = ep_order; // node index: ep order
				node0.priority_value = ep_EventTime_list[ep_order]; // priority: ep_EventTime
				handle_ep[ep_order] = C_ep_PQ[i].push(node0); // put this ep into cluster i
				ep_order++;
				// the second ep
				ep_v1_list[ep_order] = j;
				ep_v2_list[ep_order] = i;
				ep_EventTime_list[ep_order] = ep_EventTime_list[ep_order - 1] * (distribution_ratio - 1); // halve the edge cost
				ep_ep2_order_list[ep_order] = ep_order - 1; // it points to the ep above
				node0.index = ep_order; // node index: ep order
				node0.priority_value = ep_EventTime_list[ep_order]; // priority: ep_EventTime
				handle_ep[ep_order] = C_ep_PQ[j].push(node0); // put this ep into cluster j
				ep_order++;
			}
			
		}

		// for active cluster
		if (get(boost::vertex_name_t(), input_graph, i) > 0) {
			Active_C_num++; // the number of active clusters
			C_activity[i] = true; // this cluster is active
			C_event_time[i] = get(boost::vertex_name_t(), input_graph, i); // the event time is the node weight
			// push node into C_event_PQ
			node0.index = i; // node index: cluster order
			node0.priority_value = C_event_time[i]; // priority: node weight
			handle_Cevent[i] = C_event_PQ.push(node0); // into PQ
			// all the ep for cluster i have been inserted into C_ep_PQ[i]; Note that, it's only true when i starts from 0 and j>i above
			// push node into E_event_PQ
			node0.priority_value = C_ep_PQ[i].top().priority_value; // priority: the closest ep time
			handle_Eevent[i] = E_event_PQ.push(node0); // into PQ

			//cout << "C_ep_PQ[i].size():" << C_ep_PQ[i].size() << endl;
			//cout << "C_ep_PQ[i].top().priority_value:" << C_ep_PQ[i].top().priority_value << endl;
			//cout << "node0.priority_value:" << node0.priority_value << endl;
			//cout << "E_event_PQ.size():" << E_event_PQ.size() << endl;
			//cout << "E_event_PQ.top().priority_value:" << E_event_PQ.top().priority_value << endl;
			//getchar();
		}
	}


	if (target_k > Active_C_num) {
		cout << "target_k > Active_C_num! You should set a smaller target_k!" << endl;
		getchar();
		exit(1); // end the program
	}
	else if (target_k == Active_C_num) {

		int ID = 0;

		for (int i = 0; i < N; i++) {
			if (get(boost::vertex_name_t(), input_graph, i) > 0) { // vertices with positive node weights
				solution_trees[ID].first.insert(solution_trees[ID].first.end(), i);
				ID++;
				// solution_trees[i] is the ith tree; solution_trees[i].first is the vector of included vertices
			}
		}

		return solution_trees;

	}
	else { // target_k < Active_C_num


		// FGW growth starts!
		int C0, C1, C2, ep1, ep2;
		double Tc, Te, r, lowerbound = 1e-7;  // d is not used in this coding; it does not matter
		vector<pair<int, int>> merged_edges;
		pair<int, int> edge;

		while (Active_C_num > target_k) // stop the loop when there is only target_k active clusters left
		{
			// find the closest event
			Tc = C_event_PQ.top().priority_value; // this cluster event time
			Te = E_event_PQ.top().priority_value; // this edge event time

			if (Tc >= Te) { // edge event

				C1 = E_event_PQ.top().index; // the cluster C1 for this edge event
				ep1 = C_ep_PQ[C1].top().index; // the top ep in C1
				C2 = V_locator[ep_v2_list[ep1]]; // the cluster C2 for this edge event

				if (C1 == C2) { // the inside ep is triggered
					C_ep_PQ[C1].pop(); // pop out the inside ep
					// decrease E_event_PQ for the change of event_C1
					node0.index = C1;
					node0.priority_value = C_ep_PQ[C1].top().priority_value; // theoretically C_ep_PQ[event_C1] should not be empty
					E_event_PQ.decrease(handle_Eevent[C1], node0);
				}
				else { // the outside ep is triggered
					Global_time = Te;
					ep2 = ep_ep2_order_list[ep1];

					if (C_activity[C2] == true) { // C2 is active
						r = ep_EventTime_list[ep2] - Global_time; // the slack of the responsible edge

						if (r > lowerbound) { // r is big; d is not used in this coding
							// change two ep event time
							ep_EventTime_list[ep1] = Global_time + r / 2;
							ep_EventTime_list[ep2] = Global_time + r / 2;
							// update C_ep_PQ in C1
							node0.index = ep1;
							node0.priority_value = ep_EventTime_list[ep1];
							C_ep_PQ[C1].decrease(handle_ep[ep1], node0);
							// update C_ep_PQ in C2
							node0.index = ep2;
							node0.priority_value = ep_EventTime_list[ep2];
							C_ep_PQ[C2].increase(handle_ep[ep2], node0);
							// update E_event_PQ for the change of C1
							node0.index = C1;
							node0.priority_value = C_ep_PQ[C1].top().priority_value;
							E_event_PQ.decrease(handle_Eevent[C1], node0);
							// update E_event_PQ for the change of C2
							if (C_ep_PQ[C2].top().index == ep2) {
								node0.index = C2;
								node0.priority_value = C_ep_PQ[C2].top().priority_value;
								E_event_PQ.increase(handle_Eevent[C2], node0);
							}
						}
						else { // r is small; merge event

							merged_edges.insert(merged_edges.end(), { ep_v1_list[ep1] ,ep_v1_list[ep2] }); // merge edge 

							// merge V_list of C2 into C1
							C_V_list[C1].insert(end(C_V_list[C1]), begin(C_V_list[C2]), end(C_V_list[C2]));
							//decrease V_locator
							for (int i = 0; i < C_V_list[C2].size(); i++) {
								V_locator[C_V_list[C2][i]] = C1;
							}
							// update event time of C1
							C_event_time[C1] = C_event_time[C1] + C_event_time[C2] - Global_time;
							// minus one active cluster
							Active_C_num--;
							C_activity[C2] = false;
							// merge two C_ep_PQ
							C_ep_PQ[C1].pop(); // pop out the responsible ep
							C_ep_PQ[C1].merge(C_ep_PQ[C2]);
							//fibonacci_heap<node>().swap(C_ep_PQ[C2]);
							// update C1 in C_event_time and E_event_time
							node0.index = C1;
							node0.priority_value = C_event_time[C1];
							C_event_PQ.decrease(handle_Cevent[C1], node0);
							node0.priority_value = C_ep_PQ[C1].top().priority_value;
							E_event_PQ.decrease(handle_Eevent[C1], node0);
							// remove C2 from C_event_time and E_event_time
							C_event_PQ.erase(handle_Cevent[C2]);
							E_event_PQ.erase(handle_Eevent[C2]);
						}
					}
					else { // C2 is inactive
						r = ep_EventTime_list[ep2] - C_event_time[C2]; // the slack of the responsible edge

						if (r > lowerbound) { // r is big; d is not used in this coding
							// change two ep event time
							ep_EventTime_list[ep1] = Global_time + r;
							ep_EventTime_list[ep2] = C_event_time[C2];
							// update C_ep_PQ in C1
							node0.index = ep1;
							node0.priority_value = ep_EventTime_list[ep1];
							C_ep_PQ[C1].decrease(handle_ep[ep1], node0);
							// update C_ep_PQ in C2
							node0.index = ep2;
							node0.priority_value = ep_EventTime_list[ep2];
							C_ep_PQ[C2].increase(handle_ep[ep2], node0);
							// update E_event_PQ for the change of C1
							node0.index = C1;
							node0.priority_value = C_ep_PQ[C1].top().priority_value;
							E_event_PQ.decrease(handle_Eevent[C1], node0);
						}
						else { // r is small; merge event

							merged_edges.insert(merged_edges.end(), { ep_v1_list[ep1] ,ep_v1_list[ep2] }); // merge edge 

							// merge V_list of C2 into C1
							C_V_list[C1].insert(end(C_V_list[C1]), begin(C_V_list[C2]), end(C_V_list[C2]));
							//decrease V_locator
							for (int i = 0; i < C_V_list[C2].size(); i++) {
								V_locator[C_V_list[C2][i]] = C1;
							}
							// merge two C_ep_PQ
							C_ep_PQ[C1].pop(); // pop out the responsible ep		   
							typename pairing_heap<node>::iterator begin = C_ep_PQ[C2].begin();
							typename pairing_heap<node>::iterator end = C_ep_PQ[C2].end();
							for (typename pairing_heap<node>::iterator it = begin; it != end; ++it)
							{
								node0 = *it;
								if (V_locator[ep_v2_list[node0.index]] != C1) { // only push outside nodes into C_ep_PQ[event_C1]; it's a little faster than not do that
									node0.priority_value = node0.priority_value + Global_time - C_event_time[C2]; // decrease priority values
									handle_ep[node0.index] = C_ep_PQ[C1].push(node0); // push; decrease handle
								}
							}

							// decrease C1 in E_event_time
							node0.index = C1;
							node0.priority_value = C_ep_PQ[C1].top().priority_value;
							E_event_PQ.decrease(handle_Eevent[C1], node0);
						}
					}
				}
			}
			else { // cluster event
				Global_time = Tc; // decrease time
				C0 = C_event_PQ.top().index; // the cluster for this cluster event
				Active_C_num--; // minus one active cluster
				C_event_PQ.pop(); // remove the cluster from C_event_PQ
				E_event_PQ.erase(handle_Eevent[C0]); // remove the cluster from E_event_PQ
				C_activity[C0] = false; // deactivate it
			}
		}


		// output solution_trees
		int trees_ID = 0;
		vector<int> V_locator_in_trees(N, N + 1); // the index of a vertex in the trees, each element has an initial value of N+1
		for (int i = 0; i < N; i++) {
			if (C_activity[i]) { // an active cluster is a tree

				if (C_V_list[i].size() == 0) { // this should never be triggered
					cout << "C_V_list[i].size() == 0! This is an empty tree!" << endl;
					getchar();
					exit(1); // end the program
				}

				solution_trees[trees_ID].first.insert(end(solution_trees[trees_ID].first), begin(C_V_list[i]), end(C_V_list[i]));
				// solution_trees[trees_ID].first is the included_vertices list for the ith tree; this is to merge C_V_list[i] to solution_trees[trees_ID].first
				for (int j = 0; j < C_V_list[i].size(); j++) {
					V_locator_in_trees[C_V_list[i][j]] = trees_ID; // C_V_list[i][j] is in the trees_ID tree
				}
				trees_ID++; // change to next tree
			}
		}
		 
		if (trees_ID != target_k) { // this should never be triggered
			cout << "trees_ID != target_k! There is not enough tree!" << endl;
			getchar();
			exit(1); // end the program
		}


		for (int i = 0; i < merged_edges.size(); i++) {
			int target_treeID = V_locator_in_trees[merged_edges[i].first]; // merged_edges[i].first is in the target_treeID tree
			if (target_treeID != N + 1) { // this merged edge is in an active tree
				solution_trees[target_treeID].second.insert(solution_trees[target_treeID].second.end(), merged_edges[i]);
				// merge edge merged_edges[i] into solution_trees[target_treeID].second, which is the list of included_edges
			}
		}

		return solution_trees;

	}



}
#pragma endregion FGW_growth_forest  

#pragma region
vector<pair<vector<int>, vector<pair<int, int>>>> random_spanningtrees(graph& input_graph) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;

	/*input_graph may be disconnected*/

	int N = num_vertices(input_graph); // number of vertices

	/*find components in input_graph; the components info does not change after finding MST;
	this is to give indexs for saving multiple trees*/
	std::vector<int> component(N); // vertex i is in component[i]; No.component from 0
	int cpn_num = connected_components(input_graph, &component[0]); // the number of component; decrease component
	vector<pair<vector<int>, vector<pair<int, int>>>> solution_trees(cpn_num); // the solution trees: pair<included_vertices,included_edges>
	for (int i = 0; i < N; i++) {
		int treeID = component[i]; // i is in treeID tree 
		solution_trees[treeID].first.insert(solution_trees[treeID].first.end(), i); // put i into treeID tree 
		// solution_trees[treeID].first is the vector of included vertices
	}

	
	/*a new graph with random edge costs*/
	double ec_min = 1, ec_max = 10;
	graph new_graph(N);
	for (int i = 0; i < N; i++) {
		boost::tie(ai, a_end) = boost::adjacent_vertices(i, input_graph);
		for (; ai != a_end; ai++) {
			int new_cost = ec_min + (rand() % (int)(ec_max - ec_min + 1)); // generate int random number 
			boost::add_edge(i, *ai, new_cost, new_graph); // add edges random edge costs
		}
	}

	/*add dummy vertices and edges for disconnected input_graph*/
	double M = 1e20; // we assume that M is large enough to find MSTs in input_graph
	boost::add_vertex(N, new_graph); // add a dummy vertex
	for (int i = 0; i < N; i++) {
		boost::add_edge(N, i, M, new_graph); // add dummy edges
	}

	//cout << "print_vertices_and_edges(new_graph):" << endl;
	//print_vertices_and_edges(new_graph);


	/*find the random MST; https://www.boost.org/doc/libs/1_46_1/libs/graph/doc/prim_minimum_spanning_tree.html */
	std::vector <boost::graph_traits<graph>::vertex_descriptor> p(N+1); // minimum_spanning_tree traits
	prim_minimum_spanning_tree(new_graph, &p[0]); // 0 is the root; find MST in new_graph
	for (int i = 1; i < N; i++) { // p[0]=0; If p[u] = u then u is either the root of the tree or is a vertex that is not reachable from the root. 
		if (p[i] != N) { // this is not a dummy edge
			int treeID = component[i]; // i is in treeID tree
			solution_trees[treeID].second.insert(solution_trees[treeID].second.end(), { i, p[i] }); // put (i, p[i]) into treeID tree 
		}
	}

	return solution_trees;

}
#pragma endregion random_spanningtrees

#pragma region
vector<pair<vector<int>, vector<pair<int, int>>>> smart_spanningtrees
(graph& input_graph, vector<bool>& query_nodes) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;

	/*input_graph may be disconnected*/

	int N = num_vertices(input_graph); // number of vertices

	/*find components; the components info does not change after finding MST;
	this is to give indexs for saving multiple trees*/
	std::vector<int> component(N); // vertex i is in component[i]; No.component from 0
	int cpn_num = connected_components(input_graph, &component[0]); // the number of component; decrease component
	vector<pair<vector<int>, vector<pair<int, int>>>> solution_trees(cpn_num); // the solution trees: pair<included_vertices,included_edges>
	for (int i = 0; i < N; i++) {
		int treeID = component[i]; // i is in treeID tree 
		solution_trees[treeID].first.insert(solution_trees[treeID].first.end(), i); // put i into treeID tree 
		// solution_trees[treeID].first is the vector of included vertices
	}

	
	/*a new graph with random edge costs*/
	graph new_graph(N);
	for (int i = 0; i < N; i++) {
		boost::tie(ai, a_end) = boost::adjacent_vertices(i, input_graph);
		for (; ai != a_end; ai++) {
			int new_cost = 2 - query_nodes[i] - query_nodes[*ai]; // generate smart edge cost
			boost::add_edge(i, *ai, new_cost, new_graph); // add edges random edge costs
		}
	}

	/*add dummy vertices and edges for disconnected input_graph*/
	double M = 1e20; // we assume that M is large enough to find MSTs in input_graph
	boost::add_vertex(N, new_graph); // add a dummy vertex
	for (int i = 0; i < N; i++) {
		boost::add_edge(N, i, M, new_graph); // add dummy edges
	}

	/*find the random MST; https://www.boost.org/doc/libs/1_46_1/libs/graph/doc/prim_minimum_spanning_tree.html */
	std::vector <boost::graph_traits<graph>::vertex_descriptor> p(N+1); // minimum_spanning_tree traits
	prim_minimum_spanning_tree(new_graph, &p[0]); // 0 is the root; find MST in new_graph
	for (int i = 1; i < N; i++) { // p[0]=0; If p[u] = u then u is either the root of the tree or is a vertex that is not reachable from the root. 
		if (p[i] != N) { // (i, p[i]) is not a dummy edge
			int treeID = component[i]; // i is in treeID tree
			solution_trees[treeID].second.insert(solution_trees[treeID].second.end(), { i, p[i] }); // put (i, p[i]) into treeID tree 
		}
	}

	return solution_trees;

}
#pragma endregion smart_spanningtrees

#pragma region
vector<pair<vector<int>, vector<pair<int, int>>>> breadth_first_searchtrees
(graph& input_graph, vector<bool>& query_nodes, int root_query_node) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;

	/*input_graph may be disconnected*/

	int N = num_vertices(input_graph);
	std::vector<int> component(N); // vertex i is in component[i]; No.component from 0
	int cpn_num = connected_components(input_graph, &component[0]); // the number of component

	/*record the query nodes in each component*/
	vector<vector<int>> query_nodes_in_components(cpn_num);
	for (int i = 0; i < N; i++) {
		if (query_nodes[i] == true) { // i is a query node
			query_nodes_in_components[component[i]].insert
			(query_nodes_in_components[component[i]].end(), i); // i is in query_nodes_in_components[component[i]]
		}
	}


	/*add dummy edges to input_graph*/
	vector<pair<int, int>> dummy_edges;
	for (int j = 0; j < cpn_num; j++) {
		if (j != component[root_query_node]) { // j is a different component
			if (query_nodes_in_components[j].size() > 0) { // there is a query node in component j
				int random_ID = rand() % (int)(query_nodes_in_components[j].size()); // generate int random number 
				int random_querynode = query_nodes_in_components[j][random_ID]; // a random query node in component j
				boost::add_edge(root_query_node, random_querynode, -100, input_graph); // add dummy edge (i, random_querynode) with cost -100 to connect component j
				dummy_edges.insert(dummy_edges.end(), { root_query_node, random_querynode }); // record dummy edge
				//cout << "add edge(" << root_query_node << "," << random_querynode << ")" << endl;
			}
			/*if query_nodes_in_components[j].size() = 0, then there is no query node in component j,
			and we keep this component disconnected with i*/
		}
	}


	/*breadth_first_search from root_query_node; input_graph may be disconnected, and the disconnected components
	from i do not contain query nodes; bfs_edges do not contain edges in such components;
	we consider this as OK, as there is no bump (positive node weight) in such components*/
	vector<pair<int, int>> bfs_edges = boost_graph_breadth_first_search_a_tree_of_edges(input_graph, root_query_node);
	//cout << "bfs_edges.size(): " << bfs_edges.size() << endl;
	/*remove dummy edges from bfs_edges*/
	for (int j = 0; j < bfs_edges.size(); j++) {
		double cost = get(boost::edge_weight_t(), input_graph,
			boost::edge(bfs_edges[j].first, bfs_edges[j].second, input_graph).first);
		if (cost == -100) { // this is a dummy edge
			bfs_edges.erase(bfs_edges.begin() + j); // remove dummy edge from bfs_edges
			j--; // check the jth edge in bfs_edges again
		}
	}
	//cout << "bfs_edges.size(): " << bfs_edges.size() << endl;
	/*remove dummy edge from input_graph*/
	for (int j = 0; j < dummy_edges.size(); j++) {
		//cout << "remove edge(" << dummy_edges[j].first << "," << dummy_edges[j].second << ")" << endl;
		boost::remove_edge(dummy_edges[j].first, dummy_edges[j].second, input_graph);
	}

	/*bfs_edges is now the bfs trees rooted at query node i; it's not a spanning trees, as disconnected components
	with no query node are not traversed; but it's OK*/
	/*build new_graph*/
	graph new_graph(N);
	for (int j = 0; j < bfs_edges.size(); j++) {
		boost::add_edge(bfs_edges[j].first, bfs_edges[j].second, new_graph);
		//cout << "new_graph add edge(" << bfs_edges[j].first << "," << bfs_edges[j].second << ")" << endl;
	}
	std::vector<int> new_component(N);
	int new_cpn_num = connected_components(new_graph, &new_component[0]); // vertices in disconnected components are singular vertices
	/*build bfs_trees*/
	vector<pair<vector<int>, vector<pair<int, int>>>> bfs_trees(new_cpn_num); // there are new_cpn_num independent trees
	for (int i = 0; i < N; i++) {
		int cpn_ID = new_component[i];
		bfs_trees[cpn_ID].first.insert(bfs_trees[cpn_ID].first.end(), i); // insert vertex
		boost::tie(ai, a_end) = boost::adjacent_vertices(i, new_graph);
		for (; ai != a_end; ai++) {
			if (*ai > i) { // do not count an edge twice
				bfs_trees[cpn_ID].second.insert(bfs_trees[cpn_ID].second.end(), { i,*ai }); // insert edge
			}
		}
	}

	return bfs_trees;



}
#pragma endregion breadth_first_searchtrees


// ABHA subgraph_unordered_map

#pragma region
pair < vector<int>, vector<pair<int, int>>> identify_the_tree_component(graph& trees_graph, int& root) {

	/*time complexity: O(|V|)*/

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;


	pair < vector<int>, vector<pair<int, int>>> new_tree;
	int initial_N = num_vertices(trees_graph);
	vector<int> to_be_added_v;
	vector<int> added(initial_N); // /*time complexity: O(|V|)*/ this is slow, but it seems necessary

	new_tree.first.insert(new_tree.first.end(), root); // add root into this tree
	added[root] = 1;
	boost::tie(ai, a_end) = boost::adjacent_vertices(root, trees_graph); // adj vertices in trees_graph
	for (; ai != a_end; ai++) {
		to_be_added_v.insert(to_be_added_v.end(), *ai); // *ai is to_be_added_v
		new_tree.second.insert(new_tree.second.end(), { root, *ai }); // add edge
	}

	/*add new vertices and edges*/
	while (to_be_added_v.size() > 0) {
		new_tree.first.insert(new_tree.first.end(), to_be_added_v[0]); // add to_be_added_v[0] into this tree
		added[to_be_added_v[0]] = 1;
		boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_added_v[0], trees_graph); // adj vertices in trees_graph
		for (; ai != a_end; ai++) {
			if (added[*ai] == 0) {
				to_be_added_v.insert(to_be_added_v.end(), *ai); // *ai is to_be_added_v
				new_tree.second.insert(new_tree.second.end(), { to_be_added_v[0], *ai }); // add edge
			}
		}
		to_be_added_v.erase(to_be_added_v.begin()); // pop out to_be_added_v[0]
	}

	return new_tree;

}
#pragma endregion identify_the_tree_component

#pragma region
pairing_heap<node_max_heaps_edge_index> push_trees_edges_into_a_queue
(vector<pair<vector<int>, vector<pair<int, int>>>>& solution_trees, graph& initial_graph) {

	pairing_heap<node_max_heaps_edge_index> EdgeQueue; // a max priority queue
	node_max_heaps_edge_index EdgeQueue_node;

	for (int i = 0; i < solution_trees.size(); i++) {
		for (int j = 0; j < solution_trees[i].second.size(); j++) {
			int v1 = solution_trees[i].second[j].first;
			int v2 = solution_trees[i].second[j].second;
			double ec = get(boost::edge_weight_t(), initial_graph, boost::edge(v1, v2, initial_graph).first);
			EdgeQueue_node.index = solution_trees[i].second[j];
			EdgeQueue_node.priority_value = ec;
			EdgeQueue.push(EdgeQueue_node); /*put edges into a max Queue*/
		}
	}

	return EdgeQueue;

}
#pragma endregion push_trees_edges_into_a_queue

#pragma region
graph build_trees_graph_only_with_edges(int& N, vector<pair<vector<int>, vector<pair<int, int>>>>& input_trees) {

	graph input_trees_graph(N);
	for (int i = 0; i < input_trees.size(); i++) {
		for (int j = 0; j < input_trees[i].second.size(); j++) {
			int v1 = input_trees[i].second[j].first;
			int v2 = input_trees[i].second[j].second;
			boost::add_edge(v1, v2, input_trees_graph); // add edge into input_trees_graph
		}
	}

	return input_trees_graph;

}
#pragma endregion build_trees_graph_only_with_edges

#pragma region
int find_treeID_of_a_vertex_in_a_forest(int& v, vector<pair<vector<int>, vector<pair<int, int>>>>& input_trees) {

	int treeID;
	for (int i = 0; i < input_trees.size(); i++) {
		for (int j = 0; j < input_trees[i].first.size(); j++) {
			if (input_trees[i].first[j] == v) {
				treeID = i; // v_top is in input_trees[treeID]
				break;
			}
		}
	}
	return treeID;

}
#pragma endregion find_treeID_of_a_vertex_in_a_forest

#pragma region
subgraph build_trees_graph_subgraph_unordered_map(vector<pair<vector<int>, vector<pair<int, int>>>>& input_trees) {

	subgraph trees;

	for (int i = 0; i < input_trees.size(); i++) {
		for (int j = 0; j < input_trees[i].first.size(); j++) {
			int v = input_trees[i].first[j];
			subgraph_add_vertex(trees, v);
		}
		for (int j = 0; j < input_trees[i].second.size(); j++) {
			int v1 = input_trees[i].second[j].first;
			int v2 = input_trees[i].second[j].second;
			subgraph_add_edge(trees, v1, v2);
		}
	}

	return trees;

}
#pragma endregion build_trees_graph_subgraph_unordered_map

#pragma region
void push_trees_roots_into_Q_subgraph_unordered_map(vector<pair<vector<int>, vector<pair<int, int>>>>& input_trees, 
	subgraph& input_trees_graph, graph& initial_graph,
	pairing_heap<node_max_heaps_int_index>& Queue) {

	/*initialize nw values, unprocessed, processing_degree*/
	unordered_map<int, double> nw;
	unordered_map<int, int> unprocessed, processing_degree;
	for (int i = 0; i < input_trees.size(); i++) {
		for (int j = 0; j < input_trees[i].first.size(); j++) {
			int v = input_trees[i].first[j];
			nw[v] = get(boost::vertex_name_t(), initial_graph, v); // initial nw values are prizes
			unprocessed[v] = 1; // all the vertices in trees are unprocessed initially
		}
		for (int j = 0; j < input_trees[i].second.size(); j++) {
			int v1 = input_trees[i].second[j].first;
			int v2 = input_trees[i].second[j].second;
			processing_degree[v1] = 0; /*initialize processing_degree*/
			processing_degree[v2] = 0;
		}
	}
	for (int i = 0; i < input_trees.size(); i++) {
		for (int j = 0; j < input_trees[i].second.size(); j++) {
			int v1 = input_trees[i].second[j].first;
			int v2 = input_trees[i].second[j].second;
			processing_degree[v1]++; 
			processing_degree[v2]++;
		}
	}


	/*update nw values without root*/
	vector<int> target_vertex; // vertices which are unprocessed and have a processing_degree of 1
	for (int i = 0; i < input_trees.size(); i++) {
		for (int j = 0; j < input_trees[i].first.size(); j++) {
			int v = input_trees[i].first[j];
			if (processing_degree[v] == 1 && unprocessed[v] == 1) {
				target_vertex.insert(target_vertex.end(), v);
			}
		}
	}
	while (target_vertex.size() > 0) { // end the process until there is no target vertex any more
		int v = target_vertex[0]; // processing target_vertex[0]
		std::list<int> adj_vertices = subgraph_adjacent_vertices(input_trees_graph, v);
		for (std::list<int>::iterator it = adj_vertices.begin(); it != adj_vertices.end(); it++) {
			int adj_v = *it;
			if (unprocessed[adj_v] == 1) { // adj_v is unprocessed, so adj_v is v_adj
				double ec = get(boost::edge_weight_t(), initial_graph, boost::edge(v, adj_v, initial_graph).first);
				if (ec < nw[v]) {
					nw[adj_v] = nw[adj_v] + nw[v] - ec; // update nw[adj_v]
				}
				unprocessed[v] = 0; // mark v as processed
				processing_degree[adj_v]--; // update processing_degree[adj_v]
				if (processing_degree[adj_v] == 1) { // adj_v becomes a new target_vertex
					target_vertex.insert(target_vertex.end(), adj_v);
				}
				break; // there is at most one v_adj (finally, target_vertex[0] is the remaining unprocessed vertex)
			}
		}
		target_vertex.erase(target_vertex.begin()); // erase target_vertex[0]
	}

	/*push_trees_roots_into_Q*/
	node_max_heaps_int_index Queue_node;
	for (int i = 0; i < input_trees.size(); i++) {
		int root;
		double nw_root = -1;
		for (int j = 0; j < input_trees[i].first.size(); j++) {
			int v = input_trees[i].first[j];
			if (nw_root < nw[v]) {
				nw_root = nw[v];
				root = v;
			}
		}
		Queue_node.index = root;
		Queue_node.priority_value = nw_root;
		Queue.push(Queue_node);
		//cout << "Hegde_2015 nw_root: " << nw_root << endl;
		//if (nw_root > 0) {
		//	Queue.push(Queue_node);
		//}

	}


	//cout << "push_trees_roots_into_Q_subgraph_unordered_map:" << endl;
	//subgraph_print(input_trees_graph);

}
#pragma endregion push_trees_roots_into_Q_subgraph_unordered_map

#pragma region
pair < vector<int>, vector<pair<int, int>>> identify_the_tree_component_subgraph_unordered_map(subgraph& trees_graph, int& root) {

	/*time complexity: O(|V|)*/

	pair < vector<int>, vector<pair<int, int>>> new_tree;
	vector<int> to_be_added_v;
	unordered_map<int, int> added;

	new_tree.first.insert(new_tree.first.end(), root); // add root into this tree
	added[root] = 1;
	std::list<int> adj_vertices = subgraph_adjacent_vertices(trees_graph, root); // adj vertices in trees_graph
	for (std::list<int>::iterator it = adj_vertices.begin(); it != adj_vertices.end(); it++) {
		to_be_added_v.insert(to_be_added_v.end(), *it); // *ai is to_be_added_v
		new_tree.second.insert(new_tree.second.end(), { root, *it }); // add edge
	}

	/*add new vertices and edges*/
	while (to_be_added_v.size() > 0) {
		new_tree.first.insert(new_tree.first.end(), to_be_added_v[0]); // add to_be_added_v[0] into this tree
		added[to_be_added_v[0]] = 1;
		std::list<int> adj_vertices = subgraph_adjacent_vertices(trees_graph, to_be_added_v[0]); // adj vertices in trees_graph
		for (std::list<int>::iterator it = adj_vertices.begin(); it != adj_vertices.end(); it++) {
			if (added[*it] != 1) {
				to_be_added_v.insert(to_be_added_v.end(), *it); // *ai is to_be_added_v
				new_tree.second.insert(new_tree.second.end(), { to_be_added_v[0], *it }); // add edge
			}
		}
		to_be_added_v.erase(to_be_added_v.begin()); // pop out to_be_added_v[0]
	}

	return new_tree;

}
#pragma endregion identify_the_tree_component_subgraph_unordered_map

#pragma region
void add_a_bump_with_root_subgraph_unordered_map(vector<pair<vector<int>, vector<pair<int, int>>>>& input_trees, 
	subgraph& input_trees_graph, graph& initial_graph, int& root,
	vector<pair<vector<int>, vector<pair<int, int>>>>& solution_trees, vector<pair<vector<int>, 
	vector<pair<int, int>>>>& new_trees) {

	//cout << "root: " << root << endl;
	//subgraph_print(input_trees_graph);

	/*find the tree with root; root is in input_trees[treeID]*/
	int treeID = find_treeID_of_a_vertex_in_a_forest(root, input_trees);

	/*initialize nw values, unprocessed, processing_degree*/
	unordered_map<int, double> nw;
	unordered_map<int, int> unprocessed, processing_degree;
	for (int j = 0; j < input_trees[treeID].first.size(); j++) {
		int v = input_trees[treeID].first[j];
		nw[v] = get(boost::vertex_name_t(), initial_graph, v); // initial nw values are prizes
		unprocessed[v] = 1; // all the vertices in trees are unprocessed initially
	}
	for (int j = 0; j < input_trees[treeID].second.size(); j++) {
		int v1 = input_trees[treeID].second[j].first;
		int v2 = input_trees[treeID].second[j].second;
		processing_degree[v1] = 0; /*initialize processing_degree*/
		processing_degree[v2] = 0;
	}
	for (int j = 0; j < input_trees[treeID].second.size(); j++) {
		int v1 = input_trees[treeID].second[j].first;
		int v2 = input_trees[treeID].second[j].second;
		processing_degree[v1]++;
		processing_degree[v2]++;
	}

	//cout << "here1" << endl;
	//subgraph_print(input_trees_graph);

	/*update nw values with root*/
	vector<int> target_vertex; // vertices which are unprocessed and have a processing_degree of 1
	for (int j = 0; j < input_trees[treeID].first.size(); j++) {
		int v = input_trees[treeID].first[j];
		if (processing_degree[v] == 1 && unprocessed[v] == 1 && v != root) {
			target_vertex.insert(target_vertex.end(), v);
		}
	}
	while (target_vertex.size() > 0) { // end the process until there is no target vertex any more
		int v = target_vertex[0]; // processing target_vertex[0]
		std::list<int> adj_vertices = subgraph_adjacent_vertices(input_trees_graph, v);
		for (std::list<int>::iterator it = adj_vertices.begin(); it != adj_vertices.end(); it++) {
			int adj_v = *it;
			if (unprocessed[adj_v] == 1) { // *ai is unprocessed, so adj_v is v_adj
				double ec = get(boost::edge_weight_t(), initial_graph, boost::edge(v, adj_v, initial_graph).first);
				if (ec < nw[v]) {
					nw[adj_v] = nw[adj_v] + nw[v] - ec; // update nw[adj_v]
				}
				unprocessed[v] = 0; // mark v as processed
				processing_degree[adj_v]--; // update processing_degree[adj_v]
				if (processing_degree[adj_v] == 1 && adj_v != root) { // adj_v becomes a new target_vertex
					target_vertex.insert(target_vertex.end(), adj_v);
				}
				break; // there is at most one v_adj (finally, target_vertex[0] is the remaining unprocessed vertex)
			}
		}
		target_vertex.erase(target_vertex.begin()); // erase target_vertex[0]
	}

	//cout << "here2" << endl;
	//subgraph_print(input_trees_graph);

	/*roots_of_new_trees contains roots of new trees that are induced by the removel of a bump*/
	vector<int> roots_of_new_trees;

	/*to_be_removed_edges; record edges adjacent to the bump*/
	vector<pair<int, int>> to_be_removed_edges;

	/*build bump based on updated nw values; the codes below only suit nw values that are updated with a root,
	as otherwise the expensive vertices may have large nw values that are associated with adjacent vertices closer
	to the root, in which case, the expensive vertices may be incorrectly included in the pruned_tree*/
	pair<vector<int>, vector<pair<int, int>>> bump;
	bump.first.insert(bump.first.end(), root); // root is in pruned_tree
	unprocessed[root] = 2; // mark root as inserted
	vector<int> to_be_in_pruned_tree;
	std::list<int> adj_vertices = subgraph_adjacent_vertices(input_trees_graph, root);
	for (std::list<int>::iterator it = adj_vertices.begin(); it != adj_vertices.end(); it++) {
		double ec = get(boost::edge_weight_t(), initial_graph, boost::edge(root, *it, initial_graph).first);
		if (ec < nw[*it]) { // *it is worthy to be added into pruned_tree
			to_be_in_pruned_tree.insert(to_be_in_pruned_tree.end(), *it);
			bump.second.insert(bump.second.end(), { root, *it }); // {v_top, *ai} is in pruned_tree
		}
		else {
			to_be_removed_edges.insert(to_be_removed_edges.end(), { root, *it }); // do not remove *ai in its loop
			roots_of_new_trees.insert(roots_of_new_trees.end(), *it); // a new tree roots at *ai
		}
	}
	//cout << "here2.5" << endl;
	//subgraph_print(input_trees_graph);
	while (to_be_in_pruned_tree.size() > 0) {
		bump.first.insert(bump.first.end(), to_be_in_pruned_tree[0]); // to_be_in_pruned_tree[0] is in pruned_tree
		unprocessed[to_be_in_pruned_tree[0]] = 2;
		std::list<int> adj_vertices = subgraph_adjacent_vertices(input_trees_graph, to_be_in_pruned_tree[0]);
		for (std::list<int>::iterator it = adj_vertices.begin(); it != adj_vertices.end(); it++) {
			if (unprocessed[*it] != 2) {
				double ec = get(boost::edge_weight_t(), initial_graph, boost::edge(to_be_in_pruned_tree[0], 
					*it, initial_graph).first);
				if (ec < nw[*it]) { // *it is worthy to be added into pruned_tree
					to_be_in_pruned_tree.insert(to_be_in_pruned_tree.end(), *it);
					bump.second.insert(bump.second.end(), 
						{ to_be_in_pruned_tree[0], *it }); // {to_be_in_pruned_tree[0], *it} is in pruned_tree
				}
				else {
					to_be_removed_edges.insert(to_be_removed_edges.end(), { to_be_in_pruned_tree[0], *it }); // do not remove *ai in its loop
					roots_of_new_trees.insert(roots_of_new_trees.end(), *it); // a new tree roots at *ai
				}
			}
		}
		to_be_in_pruned_tree.erase(to_be_in_pruned_tree.begin()); // pop out to_be_in_pruned_tree[0]
	}


	//cout << "here3" << endl;
	//subgraph_print(input_trees_graph);

	/*add the bump to solution_trees*/
	solution_trees.insert(solution_trees.end(), bump);
	//cout << "solution_trees.insert(solution_trees.end(), bump): " << endl;
	//print_forest(solution_trees);


	/*remove bump tree from input_trees*/
	input_trees.erase(input_trees.begin() + treeID);

	/*remove bump from input_trees_graph*/
	for (int i = 0; i < bump.second.size(); i++) {
		int v1 = bump.second[i].first;
		int v2 = bump.second[i].second;
		subgraph_remove_edge_and_isolated_vertices(input_trees_graph, v1, v2);
	}

	/*remove to_be_removed_edges from input_trees_graph*/
	for (int i = 0; i < to_be_removed_edges.size(); i++) {
		int v1 = to_be_removed_edges[i].first;
		int v2 = to_be_removed_edges[i].second;
		subgraph_remove_edge_but_not_isolated_vertices(input_trees_graph, v1, v2);
	}

	/*add new trees to input_trees*/
	for (int i = 0; i < roots_of_new_trees.size(); i++) {
		pair < vector<int>, vector<pair<int, int>>> new_tree = 
			identify_the_tree_component_subgraph_unordered_map(input_trees_graph, roots_of_new_trees[i]);
		input_trees.insert(input_trees.end(), new_tree);
		new_trees.insert(new_trees.end(), new_tree);
	}


	//cout << "here4" << endl;
	//subgraph_print(input_trees_graph);


}
#pragma endregion add_a_bump_with_root_subgraph_unordered_map

#pragma region
vector<pair<vector<int>, vector<pair<int, int>>>> ABHA_subgraph_unordered_map(graph& initial_graph,
	vector<pair<vector<int>, vector<pair<int, int>>>> input_trees, int& target_k) {

	/*input_trees is changed below; so, do not make &input_trees*/

	/*time complexity: O(k|V|)*/

	vector<pair<vector<int>, vector<pair<int, int>>>> solution_trees;
	int N = num_vertices(initial_graph);

	/*build input_trees_graph*/
	subgraph input_trees_graph = build_trees_graph_subgraph_unordered_map(input_trees);

	/*a max priority queue*/
	pairing_heap<node_max_heaps_int_index> Queue;

	/*push roots of input_trees into Queue*/
	push_trees_roots_into_Q_subgraph_unordered_map(input_trees, input_trees_graph, initial_graph, Queue);


	/*hunting bumps*/
	//auto begin = std::chrono::high_resolution_clock::now();
	while (solution_trees.size() < target_k && Queue.size() > 0) { 
		// end it when solution_trees.size() = target_k or Queue.size() = 0


		//cout << "print_forest(input_trees):" << endl;
		//print_forest(input_trees);
		//cout << "print_forest(solution_trees):" << endl;
		//print_forest(solution_trees);
		//cout << "solution_trees.size(): " << solution_trees.size() << endl;
		//cout << "Queue.size(): " << Queue.size() << endl;

		/*dequeue*/
		int v_top = Queue.top().index;
		double v_top_priority = Queue.top().priority_value;
		//cout << "ABHA add Queue.top().priority_value: " << Queue.top().priority_value << endl;
		Queue.pop();

		//cout << endl;
		//cout << "v_top:" << v_top << endl;
		//cout << "v_top_priority:" << v_top_priority << endl;
		//getchar();
		//cout << endl;

		/*add a bump with v_top as the root; input_trees and input_trees_graph are updated*/
		vector<pair<vector<int>, vector<pair<int, int>>>> new_trees; // the new trees due to the removal of the bump from input_trees
		//auto begin1 = std::chrono::high_resolution_clock::now();
		add_a_bump_with_root_subgraph_unordered_map(input_trees, input_trees_graph, initial_graph, v_top, solution_trees, new_trees);
		//auto end1 = std::chrono::high_resolution_clock::now();
		//double runningtime1 = std::chrono::duration_cast<std::chrono::nanoseconds>(end1 - begin1).count() / 1e9; // s
		//cout << "add_a_bump_with_root runningtime: " << runningtime1 << endl;

		//cout << "print_forest(new_trees):" << endl;
		//print_forest(new_trees);

		/*push roots of new_trees into Queue*/
		//auto begin2 = std::chrono::high_resolution_clock::now();
		push_trees_roots_into_Q_subgraph_unordered_map(new_trees, input_trees_graph, initial_graph, Queue);
		//auto end2 = std::chrono::high_resolution_clock::now();
		//double runningtime2 = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
		//cout << "push_trees_roots_into_Q runningtime: " << runningtime2 << endl;

	}
	//auto end = std::chrono::high_resolution_clock::now();
	//double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
	//cout << "hunting bumps runningtime: " << runningtime << endl;

	//cout << "print_forest(input_trees):" << endl;
	//print_forest(input_trees);
	//cout << "print_forest(solution_trees):" << endl;
	//print_forest(solution_trees);
	//cout << "solution_trees.size(): " << solution_trees.size() << endl;
	//cout << "Queue.size(): " << Queue.size() << endl;


	//cout << "solution_trees.size(): " << solution_trees.size() << " Queue.size(): " << Queue.size() << endl;

	/*guaranteeing the target number k; time complexity: O(k|V|); in the worst case, you remove k-1 edges*/
	//auto begin1 = std::chrono::high_resolution_clock::now();
	if (solution_trees.size() < target_k) {

		/*build solution_trees_graph*/
		graph solution_trees_graph = build_trees_graph_only_with_edges(N, solution_trees);

		/*push_trees_edges_into_a_queue*/
		pairing_heap<node_max_heaps_edge_index> EdgeQueue = push_trees_edges_into_a_queue(solution_trees, initial_graph);

		/*remove largest cost edges*/
		while (solution_trees.size() < target_k) {

			/*identify the largest cost edge*/
			int v1_top = EdgeQueue.top().index.first;
			int v2_top = EdgeQueue.top().index.second;
			EdgeQueue.pop();

			/*remove initial tree from solution_trees*/
			for (int i = 0; i < solution_trees.size(); i++) {
				for (int j = 0; j < solution_trees[i].first.size(); j++) {
					int v = solution_trees[i].first[j];
					if (v == v1_top) { // the removed edge is in solution_trees[i]
						solution_trees.erase(solution_trees.begin() + i); // remove solution_trees[i]
						break;
					}
				}
			}

			/*remove edge from solution_trees_graph*/
			boost::remove_edge(v1_top, v2_top, solution_trees_graph);

			/*identify new trees*/
			pair < vector<int>, vector<pair<int, int>>> new_tree_v1_top = identify_the_tree_component(solution_trees_graph, v1_top);
			pair < vector<int>, vector<pair<int, int>>> new_tree_v2_top = identify_the_tree_component(solution_trees_graph, v2_top);

			/*add new trees to solution_trees*/
			solution_trees.insert(solution_trees.end(), new_tree_v1_top);
			solution_trees.insert(solution_trees.end(), new_tree_v2_top);

		}

	}
	//auto end1 = std::chrono::high_resolution_clock::now();
	//double runningtime1 = std::chrono::duration_cast<std::chrono::nanoseconds>(end1 - begin1).count() / 1e9; // s
	//cout << "guaranteeing the target number k runningtime: " << runningtime1 << endl;



	return solution_trees;


}
#pragma endregion ABHA_subgraph_unordered_map


// original bump hunting algorithms

#pragma region
pair<vector<int>, vector<pair<int, int>>> rooted_prunning_ec_is_one(
	vector<pair<vector<int>, vector<pair<int, int>>>>& input_trees,
	graph& input_trees_graph, graph& initial_graph, int& root) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;

	int N = num_vertices(initial_graph);

	/*find the tree with root; root is in input_trees[treeID]*/
	int treeID = find_treeID_of_a_vertex_in_a_forest(root, input_trees);

	/*initialize nw values, unprocessed, processing_degree, input_trees_graph*/
	vector<double> nw(N);
	vector<int> unprocessed(N), processing_degree(N);
	for (int j = 0; j < input_trees[treeID].first.size(); j++) {
		int v = input_trees[treeID].first[j];
		nw[v] = get(boost::vertex_name_t(), initial_graph, v); // initial nw values are prizes
		unprocessed[v] = 1; // all the vertices in trees are unprocessed initially
	}
	for (int j = 0; j < input_trees[treeID].second.size(); j++) {
		int v1 = input_trees[treeID].second[j].first;
		int v2 = input_trees[treeID].second[j].second;
		processing_degree[v1]++; /*initialize processing_degree*/
		processing_degree[v2]++;
	}

	/*update nw values with root*/
	vector<int> target_vertex; // vertices which are unprocessed and have a processing_degree of 1
	for (int j = 0; j < input_trees[treeID].first.size(); j++) {
		int v = input_trees[treeID].first[j];
		if (processing_degree[v] == 1 && unprocessed[v] == 1 && v != root) {
			target_vertex.insert(target_vertex.end(), v);
		}
	}
	while (target_vertex.size() > 0) { // end the process until there is no target vertex any more
		int v = target_vertex[0]; // processing target_vertex[0]
		boost::tie(ai, a_end) = boost::adjacent_vertices(v, input_trees_graph); // adj vertices in input_trees_graph
		for (; ai != a_end; ai++) {
			if (unprocessed[*ai] == 1) { // *ai is unprocessed, so *ai is v_adj
				double ec = 1; // all ec are 1, i.e., beta =0
				if (ec < nw[v]) {
					nw[*ai] = nw[*ai] + nw[v] - ec; // update nw[*ai]
				}
				unprocessed[v] = 0; // mark v as processed
				processing_degree[*ai]--; // update processing_degree[*ai]
				if (processing_degree[*ai] == 1 && *ai != root) { // *ai becomes a new target_vertex
					target_vertex.insert(target_vertex.end(), *ai);
				}
				break; // there is at most one v_adj (finally, target_vertex[0] is the remaining unprocessed vertex)
			}
		}
		target_vertex.erase(target_vertex.begin()); // erase target_vertex[0]
	}

	//cout << "print_vertices_and_edges(input_trees_graph):" << endl;
	//print_vertices_and_edges(input_trees_graph);
	//cout << "nw[11]:" << nw[11] << endl;

	/*build bump based on updated nw values; the codes below only suit nw values that are updated with a root,
	as otherwise the expensive vertices may have large nw values that are associated with adjacent vertices closer
	to the root, in which case, the expensive vertices may be incorrectly included in the pruned_tree*/
	pair<vector<int>, vector<pair<int, int>>> bump;
	bump.first.insert(bump.first.end(), root); // root is in pruned_tree
	unprocessed[root] = 2; // mark root as inserted
	vector<int> to_be_in_pruned_tree;
	boost::tie(ai, a_end) = boost::adjacent_vertices(root, input_trees_graph);
	for (; ai != a_end; ai++) {
		double ec = 1;
		if (ec < nw[*ai]) { // *ai is worthy to be added into pruned_tree
			to_be_in_pruned_tree.insert(to_be_in_pruned_tree.end(), *ai);
			bump.second.insert(bump.second.end(), { root, *ai }); // {v_top, *ai} is in pruned_tree
		}
	}
	while (to_be_in_pruned_tree.size() > 0) {
		bump.first.insert(bump.first.end(), to_be_in_pruned_tree[0]); // to_be_in_pruned_tree[0] is in pruned_tree
		unprocessed[to_be_in_pruned_tree[0]] = 2;
		boost::tie(ai, a_end) = boost::adjacent_vertices(to_be_in_pruned_tree[0], input_trees_graph);
		for (; ai != a_end; ai++) {
			if (unprocessed[*ai] != 2) {
				double ec = 1;
				if (ec < nw[*ai]) { // *ai is worthy to be added into pruned_tree
					to_be_in_pruned_tree.insert(to_be_in_pruned_tree.end(), *ai);
					bump.second.insert(bump.second.end(), { to_be_in_pruned_tree[0], *ai }); 
					// {to_be_in_pruned_tree[0], *ai} is in pruned_tree
				}
			}
		}
		to_be_in_pruned_tree.erase(to_be_in_pruned_tree.begin()); // pop out to_be_in_pruned_tree[0]
	}


	return bump;


}
#pragma endregion rooted_prunning_ec_is_one

#pragma region
pair<vector<int>, vector<pair<int, int>>> TreeOptimal(graph& initial_graph,
	vector<pair<vector<int>, vector<pair<int, int>>>>& input_trees, vector<bool>& removed) {


	pair<vector<int>, vector<pair<int, int>>> solution_tree;
	int N = num_vertices(initial_graph);

	int prunning_root_num = 10;
	vector<int> not_removed_v;
	vector<int> prunning_roots;
	// sample prunning roots
	for (int i = 0; i < N; i++) {
		if (removed[i] == false) {
			not_removed_v.insert(not_removed_v.end(), i);
		}
	}
	if (not_removed_v.size() < prunning_root_num) {
		prunning_root_num = not_removed_v.size(); // if not_removed_v.size() = 0, then this dunction return null
	}
	std::time_t now = std::time(0);
	boost::random::mt19937 gen{ static_cast<std::uint32_t>(now) };
	while (prunning_roots.size() < prunning_root_num) {
		boost::random::uniform_int_distribution<> dist{ 0, (int)(not_removed_v.size()-1) };
		int x = dist(gen);
		prunning_roots.insert(prunning_roots.end(), not_removed_v[x]);
		not_removed_v.erase(not_removed_v.begin() + x);
	}

	//cout << "TreeOptimal" << endl;

	/*build input_trees_graph*/
	graph input_trees_graph = build_trees_graph_only_with_edges(N, input_trees);

	// start prunning
	double solution_tree_nw = -1e10;
	for (int prune_ID = 0; prune_ID < prunning_root_num; prune_ID++) {

		//cout << "TreeOptimal " << prune_ID << " 0" << endl;

		int  prunning_root = prunning_roots[prune_ID];

		pair<vector<int>, vector<pair<int, int>>> a_bump = rooted_prunning_ec_is_one(
			input_trees, input_trees_graph, initial_graph, prunning_root);

		//cout << "TreeOptimal " << prune_ID << " 1" << endl;

		vector<pair<vector<int>, vector<pair<int, int>>>> x = { a_bump };
		double nw_a_bump = forest_net_weight(initial_graph, x);

		if (solution_tree_nw < nw_a_bump) {
			solution_tree_nw = nw_a_bump;
			solution_tree = copy_tree(a_bump);
		}

	}

	return solution_tree;


}
#pragma endregion TreeOptimal

#pragma region
vector<pair<vector<int>, vector<pair<int, int>>>> original_smart_ST
(graph input_graph, vector<bool>& query_nodes, int& target_k) {

	/*input_graph is changed below; so, do not make &input_graph*/

	vector<pair<vector<int>, vector<pair<int, int>>>> solu_trees;
	vector<bool> removed(query_nodes.size(), false); // vertices have been removed from input_graph

	while (solu_trees.size() < target_k) { // iteratively hunt bumps

		vector<pair<vector<int>, vector<pair<int, int>>>> smart_trees = smart_spanningtrees(input_graph, query_nodes);
		//cout << "print_forest(smart_trees):" << endl;
		//print_forest(smart_trees);

		// hunt a bump
		pair<vector<int>, vector<pair<int, int>>> a_bump = TreeOptimal(input_graph, smart_trees, removed);
		solu_trees.insert(solu_trees.end(), a_bump);

		/*remove a_bump from input_graph*/
		for (int i = 0; i < a_bump.first.size(); i++) {
			int v = a_bump.first[i];
			clear_vertex(v, input_graph); // v become isolated
			removed[v] = true; // v will not be selected as a prunning root later
		}


	}


	return solu_trees;

}
#pragma endregion original_smart_ST

#pragma region
vector<pair<vector<int>, vector<pair<int, int>>>> original_random_ST
(graph input_graph, int& target_k, int iteration_times) {

	/*input_graph is changed below; so, do not make &input_graph*/

	vector<pair<vector<int>, vector<pair<int, int>>>> solu_trees;
	vector<bool> removed(num_vertices(input_graph), false); // vertices have been removed from input_graph

	while (solu_trees.size() < target_k) { // iteratively hunt bumps

		//cout << "solu_trees.size() " << solu_trees.size() << endl;

		pair<vector<int>, vector<pair<int, int>>> tree;
		double largest_netweight = -1;
		for (int i = 0; i < iteration_times; i++) {

			//cout << "here " << i << endl;

			/*generate random trees*/
			vector<pair<vector<int>, vector<pair<int, int>>>> random_trees = random_spanningtrees(input_graph);

			//cout << "here " << i << " 0" << endl;

			// hunt a bump
			pair<vector<int>, vector<pair<int, int>>> a_bump = TreeOptimal(input_graph, random_trees, removed);

			//cout << "here " << i << " 1" << endl;

			/*update best solution*/
			vector<pair<vector<int>, vector<pair<int, int>>>> x = { a_bump };
			double netweight = forest_net_weight(input_graph, x);
			if (largest_netweight < netweight) {
				largest_netweight = netweight;
				tree = copy_tree(a_bump);
			}

		}

		solu_trees.insert(solu_trees.end(), tree);

		/*remove a_bump from input_graph*/
		for (int i = 0; i < tree.first.size(); i++) {
			int v = tree.first[i];
			clear_vertex(v, input_graph); // v become isolated
			removed[v] = true; // v will not be selected as a prunning root later
		}


	}


	return solu_trees;

}
#pragma endregion original_random_ST

#pragma region
vector<pair<vector<int>, vector<pair<int, int>>>> original_BF_ST
(graph input_graph, vector<bool>& query_nodes, int& target_k, int root_query_node_num) {

	/*input_graph is changed below; so, do not make &input_graph*/

	vector<pair<vector<int>, vector<pair<int, int>>>> solu_trees;
	vector<bool> removed(num_vertices(input_graph), false); // vertices have been removed from input_graph

	while (solu_trees.size() < target_k) { // iteratively hunt bumps



		pair<vector<int>, vector<pair<int, int>>> tree;
		double largest_netweight = -1;

		// sample root_query_nodes
		vector<int> root_query_nodes;
		vector<bool> selected(num_vertices(input_graph), false);
		std::time_t now = std::time(0);
		boost::random::mt19937 gen{ static_cast<std::uint32_t>(now) };
		boost::random::uniform_int_distribution<> dist{ 0, (int)(num_vertices(input_graph) - 1) };
		while (root_query_nodes.size() < root_query_node_num) {
			int x = dist(gen);
			if (query_nodes[x] == true & selected[x] == false) {
				root_query_nodes.insert(root_query_nodes.end(), x);
				selected[x] = true;
			}
		}


		for (int i = 0; i < root_query_node_num; i++) {

			//cout << "here" << i << endl;

			vector<pair<vector<int>, vector<pair<int, int>>>> DF_trees = breadth_first_searchtrees
			(input_graph, query_nodes, root_query_nodes[i]);

			// hunt a bump
			pair<vector<int>, vector<pair<int, int>>> a_bump = TreeOptimal(input_graph, DF_trees, removed);

			/*update best solution*/
			vector<pair<vector<int>, vector<pair<int, int>>>> x = { a_bump };
			double netweight = forest_net_weight(input_graph, x);
			if (largest_netweight < netweight) {
				largest_netweight = netweight;
				tree = copy_tree(a_bump);
			}

		}

		solu_trees.insert(solu_trees.end(), tree);

		/*remove a_bump from input_graph*/
		for (int i = 0; i < tree.first.size(); i++) {
			int v = tree.first[i];
			clear_vertex(v, input_graph); // v become isolated
			removed[v] = true; // v will not be selected as a prunning root later
		}


	}


	return solu_trees;

}
#pragma endregion original_BF_ST


// our bump hunting algorithms

#pragma region
vector<pair<vector<int>, vector<pair<int, int>>>> FGW_clustering(graph& input_graph, int& target_k) {

	/*input_graph may be disconnected; add dummy vertices and edges for disconnected input_graph;
	the reason to do this is that your FGW_growth_forest codes only suits graph where every vertex is connected by at least
	one edge, as otherwise the edge component of a singular vertex is empty, and the queue cannot pop out elements*/
	int N = num_vertices(input_graph); // number of vertices
	double M = 1e20; // we assume that M is large enough to guarantee that dummy components are not in FGW_trees
	boost::add_vertex(N, input_graph); // add a dummy vertex
	boost::put(boost::vertex_name_t(), input_graph, N, 0); // this dummy vertex has no prize and thus is inactive
	for (int i = 0; i < N; i++) {
		boost::add_edge(N, i, M, input_graph); // add dummy edges
	}


	/*generate FGW_trees*/
	vector<pair<vector<int>, vector<pair<int, int>>>> FGW_trees = FGW_growth_forest(input_graph, 2, target_k);


	/*remove dummy components from input_graph*/
	clear_vertex(N, input_graph);
	remove_vertex(N, input_graph);

	return FGW_trees;

}
#pragma endregion FGW_clustering

#pragma region
vector<pair<vector<int>, vector<pair<int, int>>>> GBHA(graph& input_graph, int& target_k,
	vector<pair<vector<int>, vector<pair<int, int>>>>& FGW_trees) {

	/*ABHA hunting bumps*/
	vector<pair<vector<int>, vector<pair<int, int>>>> bumps_trees = ABHA_subgraph_unordered_map(input_graph, FGW_trees, target_k);


	return bumps_trees;

}
#pragma endregion GBHA

#pragma region
vector<pair<vector<int>, vector<pair<int, int>>>> adapted_random_ST
(graph& input_graph, int& target_k, int iteration_times) {

	vector<pair<vector<int>, vector<pair<int, int>>>> solution_trees;
	double largest_netweight = -1;

	for (int i = 0; i < iteration_times; i++) {


		/*generate random trees*/
		//auto begin = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> random_trees = random_spanningtrees(input_graph);
		//auto end = std::chrono::high_resolution_clock::now();
		//double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
		//cout << "random_spanningtrees runningtime: " << runningtime << endl;

		//cout << "print_forest(random_trees):" << endl;
		//print_forest(random_trees);


		/*ABHA hunting bumps*/
		//auto begin7 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> bumps_trees = 
			ABHA_subgraph_unordered_map(input_graph, random_trees, target_k);
		//auto end7 = std::chrono::high_resolution_clock::now();
		//double runningtime7 = std::chrono::duration_cast<std::chrono::nanoseconds>(end7 - begin7).count() / 1e9; // s
		//cout << "ABHA runningtime: " << runningtime7 << endl;



		/*update best solution*/
		//auto begin8 = std::chrono::high_resolution_clock::now();
		double netweight = forest_net_weight(input_graph, bumps_trees);
		if (largest_netweight < netweight) {
			largest_netweight = netweight;
			solution_trees = copy_trees(bumps_trees);
		}
		//auto end8 = std::chrono::high_resolution_clock::now();
		//double runningtime8 = std::chrono::duration_cast<std::chrono::nanoseconds>(end8 - begin8).count() / 1e9; // s
		//cout << "update best solution runningtime: " << runningtime8 << endl;

	}

	return solution_trees;

}
#pragma endregion adapted_random_ST

#pragma region
vector<pair<vector<int>, vector<pair<int, int>>>> adapted_smart_ST
(graph& input_graph, vector<bool>& query_nodes, int& target_k) {

	/*generate smart_trees*/
	//auto begin = std::chrono::high_resolution_clock::now();
	vector<pair<vector<int>, vector<pair<int, int>>>> smart_trees = smart_spanningtrees(input_graph, query_nodes);
	//auto end = std::chrono::high_resolution_clock::now();
	//double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
	//cout << "smart_spanningtrees runningtime: " << runningtime << endl;

	//cout << "print_forest(smart_trees):" << endl;
	//print_forest(smart_trees);


	/*ABHA hunting bumps*/
	//auto begin7 = std::chrono::high_resolution_clock::now();
	vector<pair<vector<int>, vector<pair<int, int>>>> bumps_trees = ABHA_subgraph_unordered_map(input_graph, smart_trees, target_k);
	//auto end7 = std::chrono::high_resolution_clock::now();
	//double runningtime7 = std::chrono::duration_cast<std::chrono::nanoseconds>(end7 - begin7).count() / 1e9; // s
	//cout << "ABHA runningtime: " << runningtime7 << endl;

	return bumps_trees;

}
#pragma endregion adapted_smart_ST

#pragma region
vector<pair<vector<int>, vector<pair<int, int>>>> adapted_BF_ST
(graph& input_graph, vector<bool>& query_nodes, int& target_k, int root_query_node_num) {

	vector<pair<vector<int>, vector<pair<int, int>>>> solution_trees;
	double largest_netweight = -1;

	// sample root_query_nodes
	vector<int> root_query_nodes;
	vector<bool> selected(num_vertices(input_graph), false);
	std::time_t now = std::time(0);
	boost::random::mt19937 gen{ static_cast<std::uint32_t>(now) };
	boost::random::uniform_int_distribution<> dist{ 0, (int)(num_vertices(input_graph) - 1) };
	while (root_query_nodes.size() < root_query_node_num) {
		int x = dist(gen);
		if (query_nodes[x] == true & selected[x] == false) {
			root_query_nodes.insert(root_query_nodes.end(), x);
			selected[x] = true;
		}
	}


	for (int i = 0; i < root_query_node_num; i++) {

		//cout << "here" << i << endl;

		vector<pair<vector<int>, vector<pair<int, int>>>> DF_trees = breadth_first_searchtrees
		(input_graph, query_nodes, root_query_nodes[i]);

		//print_forest(DF_trees);

		/*ABHA hunting bumps*/
		vector<pair<vector<int>, vector<pair<int, int>>>> bumps_trees = ABHA_subgraph_unordered_map(input_graph, DF_trees, target_k);

		/*update best solution*/
		//auto begin8 = std::chrono::high_resolution_clock::now();
		double netweight = forest_net_weight(input_graph, bumps_trees);
		if (largest_netweight < netweight) {
			largest_netweight = netweight;
			solution_trees = copy_trees(bumps_trees);
		}
		//auto end8 = std::chrono::high_resolution_clock::now();
		//double runningtime8 = std::chrono::duration_cast<std::chrono::nanoseconds>(end8 - begin8).count() / 1e9; // s
		//cout << "update best solution runningtime: " << runningtime8 << endl;

	}

	return solution_trees;


}
#pragma endregion adapted_BF_ST

#pragma region
void add_a_bump_with_root_no_newtree_subgraph_unordered_map(vector<pair<vector<int>, vector<pair<int, int>>>>& input_trees,
	subgraph& input_trees_graph, graph& initial_graph, int& root,
	vector<pair<vector<int>, vector<pair<int, int>>>>& solution_trees) {

	/*find the tree with root; root is in input_trees[treeID]*/
	int treeID = find_treeID_of_a_vertex_in_a_forest(root, input_trees);

	/*initialize nw values, unprocessed, processing_degree*/
	unordered_map<int, double> nw;
	unordered_map<int, int> unprocessed, processing_degree;
	for (int j = 0; j < input_trees[treeID].first.size(); j++) {
		int v = input_trees[treeID].first[j];
		nw[v] = get(boost::vertex_name_t(), initial_graph, v); // initial nw values are prizes
		unprocessed[v] = 1; // all the vertices in trees are unprocessed initially
	}
	for (int j = 0; j < input_trees[treeID].second.size(); j++) {
		int v1 = input_trees[treeID].second[j].first;
		int v2 = input_trees[treeID].second[j].second;
		processing_degree[v1] = 0; /*initialize processing_degree*/
		processing_degree[v2] = 0;
	}
	for (int j = 0; j < input_trees[treeID].second.size(); j++) {
		int v1 = input_trees[treeID].second[j].first;
		int v2 = input_trees[treeID].second[j].second;
		processing_degree[v1]++;
		processing_degree[v2]++;
	}

	//cout << "here1" << endl;
	//subgraph_print(input_trees_graph);

	/*update nw values with root*/
	vector<int> target_vertex; // vertices which are unprocessed and have a processing_degree of 1
	for (int j = 0; j < input_trees[treeID].first.size(); j++) {
		int v = input_trees[treeID].first[j];
		if (processing_degree[v] == 1 && unprocessed[v] == 1 && v != root) {
			target_vertex.insert(target_vertex.end(), v);
		}
	}
	while (target_vertex.size() > 0) { // end the process until there is no target vertex any more
		int v = target_vertex[0]; // processing target_vertex[0]
		std::list<int> adj_vertices = subgraph_adjacent_vertices(input_trees_graph, v);
		for (std::list<int>::iterator it = adj_vertices.begin(); it != adj_vertices.end(); it++) {
			int adj_v = *it;
			if (unprocessed[adj_v] == 1) { // *ai is unprocessed, so adj_v is v_adj
				double ec = get(boost::edge_weight_t(), initial_graph, boost::edge(v, adj_v, initial_graph).first);
				if (ec < nw[v]) {
					nw[adj_v] = nw[adj_v] + nw[v] - ec; // update nw[adj_v]
				}
				unprocessed[v] = 0; // mark v as processed
				processing_degree[adj_v]--; // update processing_degree[adj_v]
				if (processing_degree[adj_v] == 1 && adj_v != root) { // adj_v becomes a new target_vertex
					target_vertex.insert(target_vertex.end(), adj_v);
				}
				break; // there is at most one v_adj (finally, target_vertex[0] is the remaining unprocessed vertex)
			}
		}
		target_vertex.erase(target_vertex.begin()); // erase target_vertex[0]
	}

	//cout << "here2" << endl;
	//subgraph_print(input_trees_graph);

	/*build bump based on updated nw values; the codes below only suit nw values that are updated with a root,
	as otherwise the expensive vertices may have large nw values that are associated with adjacent vertices closer
	to the root, in which case, the expensive vertices may be incorrectly included in the pruned_tree*/
	pair<vector<int>, vector<pair<int, int>>> bump;
	bump.first.insert(bump.first.end(), root); // root is in pruned_tree
	unprocessed[root] = 2; // mark root as inserted
	vector<int> to_be_in_pruned_tree;
	std::list<int> adj_vertices = subgraph_adjacent_vertices(input_trees_graph, root);
	for (std::list<int>::iterator it = adj_vertices.begin(); it != adj_vertices.end(); it++) {
		double ec = get(boost::edge_weight_t(), initial_graph, boost::edge(root, *it, initial_graph).first);
		if (ec < nw[*it]) { // *it is worthy to be added into pruned_tree
			to_be_in_pruned_tree.insert(to_be_in_pruned_tree.end(), *it);
			bump.second.insert(bump.second.end(), { root, *it }); // {v_top, *ai} is in pruned_tree
		}
	}
	//cout << "here2.5" << endl;
	//subgraph_print(input_trees_graph);
	while (to_be_in_pruned_tree.size() > 0) {
		bump.first.insert(bump.first.end(), to_be_in_pruned_tree[0]); // to_be_in_pruned_tree[0] is in pruned_tree
		unprocessed[to_be_in_pruned_tree[0]] = 2;
		std::list<int> adj_vertices = subgraph_adjacent_vertices(input_trees_graph, to_be_in_pruned_tree[0]);
		for (std::list<int>::iterator it = adj_vertices.begin(); it != adj_vertices.end(); it++) {
			if (unprocessed[*it] != 2) {
				double ec = get(boost::edge_weight_t(), initial_graph, boost::edge(to_be_in_pruned_tree[0],
					*it, initial_graph).first);
				if (ec < nw[*it]) { // *it is worthy to be added into pruned_tree
					to_be_in_pruned_tree.insert(to_be_in_pruned_tree.end(), *it);
					bump.second.insert(bump.second.end(),
						{ to_be_in_pruned_tree[0], *it }); // {to_be_in_pruned_tree[0], *it} is in pruned_tree
				}
			}
		}
		to_be_in_pruned_tree.erase(to_be_in_pruned_tree.begin()); // pop out to_be_in_pruned_tree[0]
	}


	//cout << "here3" << endl;
	//subgraph_print(input_trees_graph);

	/*add the bump to solution_trees*/
	solution_trees.insert(solution_trees.end(), bump);
	//cout << "solution_trees.insert(solution_trees.end(), bump): " << endl;
	//print_forest(solution_trees);

}
#pragma endregion add_a_bump_with_root_no_newtree_subgraph_unordered_map

#pragma region
vector<pair<vector<int>, vector<pair<int, int>>>> Hegde_2015(graph& initial_graph, int& target_k,
	vector<pair<vector<int>, vector<pair<int, int>>>> FGW_trees) {

	/*build input_trees_graph*/
	subgraph input_trees_graph = build_trees_graph_subgraph_unordered_map(FGW_trees);
	/*a max priority queue*/
	pairing_heap<node_max_heaps_int_index> Queue;
	/*push roots of input_trees into Queue*/
	push_trees_roots_into_Q_subgraph_unordered_map(FGW_trees, input_trees_graph, initial_graph, Queue);
	

	/*hunting a bump in each tree*/
	vector<pair<vector<int>, vector<pair<int, int>>>> bumps_trees;
	while (Queue.size() > 0) {

		/*dequeue*/
		int v_top = Queue.top().index;
		//cout << "Hegde_2015 add Queue.top().priority_value: " << Queue.top().priority_value << endl;
		Queue.pop();

		/*add a bump with v_top as the root; input_trees and input_trees_graph are updated*/
		add_a_bump_with_root_no_newtree_subgraph_unordered_map(FGW_trees, input_trees_graph,
			initial_graph, v_top, bumps_trees);

	}

	return bumps_trees;

}
#pragma endregion Hegde_2015




// input Twitter and Flickr datasets

#pragma region  
void read_Austin_graph(graph& Twitter_graph_base, std::vector<double>& Twitter_prizes, std::vector<double>& Flickr_prizes,
	std::vector<pair<double, double>>& locations) {


	int V_num, v1, v2;
	double p1, p2, l1, l2;

	string file_name = "Austin_graph.stp";
	string line_content;
	ifstream myfile(file_name); // open the file
	if (myfile.is_open()) // if the file is opened successfully
	{
		while (getline(myfile, line_content)) // read file line by line
		{
			std::vector<string> Parsed_content = parse_string(line_content, " "); // parse line_content


			if (!Parsed_content[0].compare("Nodes")) // when it's equal, compare returns 0
			{
				V_num = stoi(Parsed_content[1]); // convert string to int
				graph new_graph(V_num);
				Twitter_graph_base = copy_graph(new_graph);
			}
			else if (!Parsed_content[0].compare("V"))
			{

				p1 = stod(Parsed_content[2]);
				p2 = stod(Parsed_content[3]);
				l1 = stod(Parsed_content[5]);
				l2 = stod(Parsed_content[6]);
				Twitter_prizes.insert(Twitter_prizes.end(), p1);
				Flickr_prizes.insert(Flickr_prizes.end(), p2);
				locations.insert(locations.end(), { l1,l2 });

			}
			else if (!Parsed_content.front().compare("Edge"))
			{
				v1 = stoi(Parsed_content[1]);
				v2 = stoi(Parsed_content[2]);
				p1 = stod(Parsed_content[3]);

				boost::add_edge(v1, v2, p1, Twitter_graph_base); // add edge
			}
		}

		myfile.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl
			<< "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}
}
#pragma endregion read_Austin_graph

// input large DBLP datasets

#pragma region 
void read_DBLP_data(graph& DBLP_graph, graph& DBLP_group_graph,
	std::vector<string>& DBLP_expert_names, std::vector<string>& DBLP_skill_names) {

	std::unordered_map<std::string, int> expert_names_unordered_map; // name, ID
	std::unordered_map<std::string, int> skills_unordered_map; // skill, ID
	std::unordered_map<std::string, std::vector<string>> expert_keywords_unordered_map;

	string file_name = "DBLP_1094k_keywords.txt";
	string line_content;
	ifstream myfile(file_name); // open the file
	if (myfile.is_open()) // if the file is opened successfully
	{
		int count = 0;
		while (getline(myfile, line_content)) // read file line by line
		{
			if (count > 0) {
				std::vector<string> Parsed_content = parse_string(line_content, "	"); // parse line_content
				string author_name = Parsed_content[0];
				int author_ID = expert_names_unordered_map.size();
				expert_names_unordered_map[author_name] = author_ID;
				if (Parsed_content.size() == 2) {
					std::vector<string> skills = parse_string(Parsed_content[1], ","); // parse line_content
					expert_keywords_unordered_map[author_name] = skills;
					for (int i = 0; i < skills.size(); i++) {
						string skill_name = skills[i];
						auto search = skills_unordered_map.find(skill_name);
						if (search == skills_unordered_map.end()) { // new skill
							int skill_ID = skills_unordered_map.size();
							skills_unordered_map[skill_name] = skill_ID;
						}
					}
				}
			}
			count++;
		}
		myfile.close(); //close the file

		int N = expert_names_unordered_map.size();
		int S = skills_unordered_map.size();
		for (int i = 0; i < N; i++) {
			boost::add_vertex(i, DBLP_graph); // add vertex
			boost::add_vertex(i, DBLP_group_graph);
		}
		for (int i = 0; i < S; i++) {
			boost::add_vertex(i + N, DBLP_group_graph);
		}

		DBLP_expert_names.resize(N);
		for (auto it = expert_names_unordered_map.begin(); it != expert_names_unordered_map.end(); ++it) {
			string author = it->first;
			int ID = it->second;
			DBLP_expert_names[ID] = author;
		}

		DBLP_skill_names.resize(S);
		for (auto it = skills_unordered_map.begin(); it != skills_unordered_map.end(); ++it) {
			string skill = it->first;
			int ID = it->second;
			DBLP_skill_names[ID] = skill;
		}

		for (auto it = expert_keywords_unordered_map.begin(); it != expert_keywords_unordered_map.end(); ++it) {
			string author_name = it->first;
			std::vector<string> skills = it->second;
			int author_ID = expert_names_unordered_map[author_name];
			for (int i = 0; i < skills.size(); i++) {
				string skill_name = skills[i];
				int skill_ID = skills_unordered_map[skill_name];
				boost::add_edge(author_ID, N + skill_ID, 1, DBLP_group_graph);
			}
		}


		file_name = "DBLP_1094k_collaborations.txt";
		ifstream myfile2(file_name); // open the file
		if (myfile2.is_open()) // if the file is opened successfully
		{
			int count = 0;
			while (getline(myfile2, line_content)) // read file line by line
			{
				if (count > 0) {
					std::vector<string> Parsed_content = parse_string(line_content, ","); // parse line_content
					string author_name1 = Parsed_content[0];
					string author_name2 = Parsed_content[1];
					int e1 = expert_names_unordered_map[author_name1];
					int e2 = expert_names_unordered_map[author_name2];
					boost::add_edge(e1, e2, 1, DBLP_graph);
				}
				count++;
			}
		}
		myfile2.close(); //close the file

		int E = num_edges(DBLP_graph);

		cout << "V = " << N << " E = " << E << " S = " << S << endl;
		cout << "num_vertices(DBLP_group_graph): " << num_vertices(DBLP_group_graph) << endl;
		cout << "num_edges(DBLP_group_graph): " << num_edges(DBLP_group_graph) << endl;

	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}

}
#pragma endregion read_DBLP_data 


// Experiments bases

#pragma region
std::vector<bool> random_skills_for_querying_experts(graph& input_graph, graph& input_group_graph, int selected_skills_num) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;


	int N = num_vertices(input_graph), skill_N = num_vertices(input_group_graph) - N;

	std::vector<bool> vertex_queryed(N);


	/*randomly select skills*/
	std::vector<int> selected_skills;
	std::vector<int> skills(skill_N);
	std::iota(std::begin(skills), std::end(skills), 0); // Fill with 0, 1, ..., skill_N
	while (selected_skills.size() < selected_skills_num) {
		int ID = rand() % (int) (skills.size());
		int skill = skills[ID];
		skills.erase(skills.begin() + ID);
		selected_skills.insert(selected_skills.end(), skill);
	}

	/*query nodes*/
	for (int i = 0; i < selected_skills.size(); i++) {
		int skill = selected_skills[i];
		boost::tie(ai, a_end) = boost::adjacent_vertices(N + skill, input_group_graph);
		for (; ai != a_end; ai++) {
			vertex_queryed[*ai] = true;
		}
	}

	return vertex_queryed;

}
#pragma endregion random_skills_for_querying_experts

#pragma region
std::vector<bool> correlated_skills_for_querying_experts(graph& input_graph, graph& input_group_graph, 
	int selected_skills_num) {

	/*Two skills are correlated with each other if there is an expert who has these two skills. 
	Each pair of query skills are correlated with each other.*/

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;


	int N = num_vertices(input_graph), skill_N = num_vertices(input_group_graph) - N;

	if (selected_skills_num > skill_N) {
		cout << "Error: selected_skills_num > skill_N in correlated_skills_for_querying_experts" << endl;
		getchar();
		exit(1);
	}


	std::vector<bool> vertex_queryed(N);
	std::vector<int> selected_skills;
	std::vector<int> candidate_skills;

	/*populate candidate_skills*/
	while (1 > 0) {

		int skill_ID = rand() % (int)(skill_N); // a random query skill

		std::vector<int> experts; // experts with skill_ID
		boost::tie(ai, a_end) = boost::adjacent_vertices(N + skill_ID, input_group_graph);
		for (; ai != a_end; ai++) {
			experts.insert(experts.end(), *ai); 
		}

		bool enough = false;
		for (int i = 0; i < experts.size(); i++) {
			int expert_ID = experts[i];
			boost::tie(ai, a_end) = boost::adjacent_vertices(expert_ID, input_group_graph);
			for (; ai != a_end; ai++) {
				int skill = *ai - N; // a correlated skill
				bool added = false;
				for (int j = 0; j < candidate_skills.size(); j++) {
					if (candidate_skills[j] == skill) {
						added = true;
						break;
					}
				}
				if (added == false) { // this correlated skill is new 
					candidate_skills.insert(candidate_skills.end(), skill); // add this skill to candidate_skills
					if (candidate_skills.size() > selected_skills_num * 10) {
						enough = true;
					}
				}
				if (enough == true) {
					break;
				}
			}
			if (enough == true) {
				break;
			}
		}
		if (candidate_skills.size() >= selected_skills_num) {
			break;
		}
		else {
			cout << "selected_skills_num: "<<
				selected_skills_num << 
				" candidate_skills.size() < selected_skills_num; reselect skills ..." << endl;
			candidate_skills.clear();
		}

	}


	/*selected_skills*/
	while (selected_skills.size() < selected_skills_num) {

		int ID = rand() % (int)(candidate_skills.size());
		int skill = candidate_skills[ID];
		candidate_skills.erase(candidate_skills.begin() + ID);
		selected_skills.insert(selected_skills.end(), skill); // select a skill

	}

	/*query nodes*/
	for (int i = 0; i < selected_skills.size(); i++) {
		int skill = selected_skills[i];
		boost::tie(ai, a_end) = boost::adjacent_vertices(N + skill, input_group_graph);
		for (; ai != a_end; ai++) {
			vertex_queryed[*ai] = true;
		}
	}

	return vertex_queryed;

}
#pragma endregion correlated_skills_for_querying_experts

#pragma region
void generate_random_small_graphs_for_DBLP(graph& input_graph, graph& input_group_graph, int small_V, 
	graph& output_graph, graph& output_group_graph) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;

	int input_N = num_vertices(input_graph), input_skill_N = num_vertices(input_group_graph) - input_N;

	/*fill sampled_vertices*/
	//std::vector<int> sampled_vertices(input_N);
	//std::iota(std::begin(sampled_vertices), std::end(sampled_vertices), 0); // Fill with 0, 1, ..., input_N
	//while (sampled_vertices.size() > small_V) {
	//	int ID = rand() % (int)(sampled_vertices.size());
	//	sampled_vertices.erase(sampled_vertices.begin() + ID);
	//}
	std::vector<int> sampled_vertices(small_V);
	std::iota(std::begin(sampled_vertices), std::end(sampled_vertices), 0); // Fill with 0, 1, ..., small_V - 1


	std::vector<bool> vertex_included(input_N);
	std::vector<int> original_location_in_small(input_N); // small_location_in_original is sampled_vertices
	for (int i = 0; i < small_V; i++) {
		int v = sampled_vertices[i];
		vertex_included[v]=true;
		original_location_in_small[v] = i;
		double w = get(boost::vertex_name_t(), input_graph, v);
		boost::add_vertex(i, output_graph); // add_vertex
		boost::put(boost::vertex_name_t(), output_graph, i, w); // add_vertex weight

	}
	for (int i = 0; i < small_V; i++) {
		int v = sampled_vertices[i];
		boost::tie(ai, a_end) = boost::adjacent_vertices(v, input_graph);
		for (; ai != a_end; ai++) {
			if (vertex_included[*ai] == true && v < *ai) {
				double ec = get(boost::edge_weight_t(), input_graph, boost::edge(v, *ai, input_graph).first);
				int v1 = i;
				int v2 = original_location_in_small[*ai];
				boost::add_edge(v1, v2, ec, output_graph); // add_edge
			}
		}
	}


	std::vector<int> sampled_skills;

	/*fill sampled_skills*/
	std::vector<bool> skill_included(input_skill_N);
	std::vector<int> original_skill_location_in_small(input_skill_N);
	for (int i = 0; i < small_V; i++) {
		int v = sampled_vertices[i];
		boost::tie(ai, a_end) = boost::adjacent_vertices(v, input_group_graph);
		for (; ai != a_end; ai++) {
			skill_included[*ai - input_N] = true;
		}
	}
	for (int i = 0; i < input_skill_N; i++) {
		if (skill_included[i] == true) {
			original_skill_location_in_small[i] = sampled_skills.size();
			sampled_skills.insert(sampled_skills.end(), i);
		}
	}

	for (int i = 0; i < small_V + sampled_skills.size(); i++) {
		boost::add_vertex(i, output_group_graph); // add_vertex
	}

	for (int i = 0; i < small_V; i++) {
		int v = sampled_vertices[i];
		boost::tie(ai, a_end) = boost::adjacent_vertices(v, input_group_graph);
		for (; ai != a_end; ai++) {
			if (skill_included[*ai - input_N] == true) {
				boost::add_edge(i, small_V + original_skill_location_in_small[*ai - input_N], output_group_graph);
				//cout << "add edge " << i << " " << original_skill_location_in_small[*ai - input_N] << endl;
				//getchar();
			}
		}
	}

}
#pragma endregion generate_random_small_graphs_for_DBLP

#pragma region
void generate_random_small_graphs_for_Twitter(graph& input_graph, std::vector<double>& input_prizes, 
	int small_V, graph& output_graph, std::vector<double>& output_prizes) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;

	int input_N = num_vertices(input_graph);

	//std::vector<int> unsampled_vertices(input_N);
	//std::iota(std::begin(unsampled_vertices), std::end(unsampled_vertices), 0); // Fill with 0, 1, ..., input_N
	//std::vector<int> sampled_vertices;
	///*fill sampled_vertices*/
	//while (sampled_vertices.size() < small_V) {
	//	int ID = rand() % (int)(unsampled_vertices.size());
	//	int v = unsampled_vertices[ID];
	//	unsampled_vertices.erase(unsampled_vertices.begin() + ID);
	//	sampled_vertices.insert(sampled_vertices.end(), v);
	//}
	std::vector<int> sampled_vertices(small_V);
	std::iota(std::begin(sampled_vertices), std::end(sampled_vertices), 0); // Fill with 0, 1, ..., small_V - 1


	std::vector<bool> vertex_included(input_N);
	std::vector<int> original_location_in_small(input_N); // small_location_in_original is sampled_vertices
	for (int i = 0; i < small_V; i++) {
		int v = sampled_vertices[i];
		vertex_included[v] = true;
		original_location_in_small[v] = i;
		double w = get(boost::vertex_name_t(), input_graph, v);
		boost::add_vertex(i, output_graph); // add_vertex
		boost::put(boost::vertex_name_t(), output_graph, i, w); // add_vertex weight
	}
	for (int i = 0; i < small_V; i++) {
		int v = sampled_vertices[i];
		boost::tie(ai, a_end) = boost::adjacent_vertices(v, input_graph);
		for (; ai != a_end; ai++) {
			if (vertex_included[*ai] == true && v < *ai) {
				double ec = get(boost::edge_weight_t(), input_graph, boost::edge(v, *ai, input_graph).first);
				int v1 = i;
				int v2 = original_location_in_small[*ai];
				boost::add_edge(v1, v2, ec, output_graph); // add_edge
			}
		}
	}



	output_prizes.resize(small_V);
	for (int i = 0; i < small_V; i++) {
		int v = sampled_vertices[i];
		output_prizes[i] = input_prizes[v];
	}



}
#pragma endregion generate_random_small_graphs_for_Twitter

#pragma region
std::vector<bool> prize_LB_for_querying_nodes(std::vector<double>& prizes, double prize_LB) {

	int N = prizes.size();
	std::vector<bool> vertex_queryed(N);

	/*query nodes*/
	for (int i = 0; i < N; i++) {

		double w = prizes[i];
		if (w >= prize_LB) {
			vertex_queryed[i] = true;
		}

	}

	return vertex_queryed;

}
#pragma endregion prize_LB_for_querying_nodes

#pragma region
graph generate_PCSFP_instances(graph& input_graph, std::vector<bool>& queried_nodes, double alpha, double beta) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;

	graph instance_graph = copy_graph(input_graph);

	for (int i = 0; i < queried_nodes.size(); i++) {

		if (queried_nodes[i] == true) {
			boost::put(boost::vertex_name_t(), instance_graph, i, alpha + 1);
		}
		else {
			boost::put(boost::vertex_name_t(), instance_graph, i, 0);
		}

		boost::tie(ai, a_end) = boost::adjacent_vertices(i, instance_graph);
		for (; ai != a_end; ai++) {
			int j = *ai;
			if (i < j) {
				double ec = get(boost::edge_weight_t(), instance_graph, boost::edge(i, j, instance_graph).first);
				boost::put(boost::edge_weight_t(), instance_graph, boost::edge(i, j, instance_graph).first, beta*ec + 1);
			}
		}

	}

	return instance_graph;

}
#pragma endregion generate_PCSFP_instances

#pragma region
graph generate_DBLP_instance(graph&  intput_graph, graph& input_group_graph, int queried_skills_num, std::vector<bool>& query_nodes,
	double alpha, double beta) {


	query_nodes = correlated_skills_for_querying_experts(intput_graph, input_group_graph, queried_skills_num);

	graph instance_graph = generate_PCSFP_instances(intput_graph, query_nodes, alpha, beta);

	return instance_graph;


}
#pragma endregion generate_DBLP_instance

#pragma region
graph generate_smaller_DBLP_instance(graph& input_graph, 
	graph& input_group_graph, int small_V, int queried_skills_num, std::vector<bool>& query_nodes,
	double alpha, double beta) {

	graph small_graph, small_group_graph;

	generate_random_small_graphs_for_DBLP(input_graph, input_group_graph, small_V, small_graph, small_group_graph);

	//typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	//AdjacencyIterator ai, a_end;
	//boost::tie(ai, a_end) = boost::adjacent_vertices(0, small_group_graph);
	//for (; ai != a_end; ai++) {
	//	cout << "adj v: " << *ai << endl;
	//}


	//cout << "num_vertices(small_graph): " << num_vertices(small_graph) << endl;
	//cout << "num_vertices(small_group_graph): " << num_vertices(small_group_graph) << endl;
	//cout << "num_edges(small_group_graph): " << num_edges(small_group_graph) << endl;
	//getchar();

	query_nodes = correlated_skills_for_querying_experts(small_graph, small_group_graph, queried_skills_num);


	graph instance_graph = generate_PCSFP_instances(small_graph, query_nodes, alpha, beta);

	return instance_graph;


}
#pragma endregion generate_smaller_DBLP_instance

#pragma region
graph generate_Twitter_instance(graph&  intput_graph, std::vector<double>& prizes, double prize_LB, std::vector<bool>& query_nodes,
	double alpha, double beta) {


	query_nodes = prize_LB_for_querying_nodes(prizes, prize_LB);

	graph instance_graph = generate_PCSFP_instances(intput_graph, query_nodes, alpha, beta);

	return instance_graph;


}
#pragma endregion generate_Twitter_instance

#pragma region
graph generate_smaller_Twitter_instance(graph&  input_graph, std::vector<double>& prizes, int small_V, double prize_LB, std::vector<bool>& query_nodes,
	double alpha, double beta) {

	graph small_graph;
	std::vector<double> small_prizes;

	generate_random_small_graphs_for_Twitter(input_graph, prizes, small_V, small_graph, small_prizes);

	query_nodes = prize_LB_for_querying_nodes(small_prizes, prize_LB);

	graph instance_graph = generate_PCSFP_instances(small_graph, query_nodes, alpha, beta);

	return instance_graph;


}
#pragma endregion generate_smaller_Twitter_instance

#pragma region
void is_there_a_component_with_multiple_query_nodes(graph& input_graph, std::vector<bool>& query_nodes) {

	cout << "num_vertices(input_graph) = " << num_vertices(input_graph) << " num_edges(input_graph) = " << num_edges(input_graph) << endl;

	int N = num_vertices(input_graph);
	std::vector<int> component(N); // vertex i is in component[i]; No.component from 0
	int cpn_num = connected_components(input_graph, &component[0]); // the number of component; decrease component
	cout << "input_graph cpn_num= " << cpn_num << endl;

	std::vector<std::vector<int>> queried_nodes_cpn(cpn_num);

	int queried_num = 0;

	for (int i = 0; i < N; i++) {

		if (query_nodes[i] == true) { // this is a query node
			queried_num++;
			int cpn_ID = component[i];
			queried_nodes_cpn[cpn_ID].insert(queried_nodes_cpn[cpn_ID].end(), i);
			if (queried_nodes_cpn[cpn_ID].size() > 1) {
				cout << "query nodes " << queried_nodes_cpn[cpn_ID][0] << " and " << queried_nodes_cpn[cpn_ID][1] << " are in the same component." << endl;
				getchar();
				exit(1);
			}
		}


	}

	cout << "queried_num = " << queried_num << endl;
}
#pragma endregion is_there_a_component_with_multiple_query_nodes




// statistics; approximating the number of Concrete Bumps

#pragma region
vector<pair<vector<int>, vector<pair<int, int>>>> FGW_growth_forest_for_Concrete_Bumps
(graph& input_graph, double distribution_ratio) {


	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	graph::out_edge_iterator eit, eend;


	vector<pair<vector<int>, vector<pair<int, int>>>> solution_trees; // the solution trees: pair<included_vertices,included_edges>


	double Global_time = 0; // global time
	int Active_C_num = 0; // the number of active clusters

	int N = num_vertices(input_graph); // number of vertices
	int ep_num = num_edges(input_graph) * 2; // total number of edge parts
	int ep_order = 0;
	node node0;

	// Clusters: the number of clusters is always N
	vector<bool> C_activity(N); // activity value of each C; false means inactive; initial value is false
	vector<double> C_event_time(N); // the event time for each C
	vector<vector<int>> C_V_list(N); // record the vertices in each C
	vector<pairing_heap<node>> C_ep_PQ(N); // the PQ for edge parts in each C; node index: ep order in ep_list
	vector<int> V_locator(N); // the index of the maximal cluster containing the vertex

	// edge parts: PQ and their handles
	vector<int> ep_v1_list(ep_num); // class may be slow, so I seperate the ep_list
	vector<int> ep_v2_list(ep_num);
	vector<double> ep_EventTime_list(ep_num);
	vector<int> ep_ep2_order_list(ep_num);
	vector<handle_t> handle_ep(ep_num); // store the handle for each edge part

	// the event PQ and their handles
	pairing_heap<node> C_event_PQ; // PQ storing the event time of the active clusters; node index: cluster order
	vector<handle_t> handle_Cevent(N);
	pairing_heap<node> E_event_PQ; // PQ storing the active clusters; node index: cluster order
	vector<handle_t> handle_Eevent(N);



	// initialize the clusters
	for (int i = 0; i < N; i++)
	{
		C_V_list[i].insert(C_V_list[i].end(), i); // insert a vertex into the rear of C_V_list[i]; each vertex is a singular cluster
		V_locator[i] = i; // the maximal cluster containing vertex i


		// add edge parts into C
		boost::tie(ai, a_end) = boost::adjacent_vertices(i, input_graph); // adjacent_vertices of i
		for (; ai != a_end; ai++) {

			int j = *ai;// the adjacent vetex to i
			if (j > i) { // don't overcheck an edge
				// the first ep
				ep_v1_list[ep_order] = i;
				ep_v2_list[ep_order] = j;
				ep_EventTime_list[ep_order] = get(boost::edge_weight_t(), input_graph, boost::edge(i, j, input_graph).first) / distribution_ratio; // halve the edge cost
				ep_ep2_order_list[ep_order] = ep_order + 1; // it points to the ep below
				node0.index = ep_order; // node index: ep order
				node0.priority_value = ep_EventTime_list[ep_order]; // priority: ep_EventTime
				handle_ep[ep_order] = C_ep_PQ[i].push(node0); // put this ep into cluster i
				ep_order++;
				// the second ep
				ep_v1_list[ep_order] = j;
				ep_v2_list[ep_order] = i;
				ep_EventTime_list[ep_order] = ep_EventTime_list[ep_order - 1] * (distribution_ratio - 1); // halve the edge cost
				ep_ep2_order_list[ep_order] = ep_order - 1; // it points to the ep above
				node0.index = ep_order; // node index: ep order
				node0.priority_value = ep_EventTime_list[ep_order]; // priority: ep_EventTime
				handle_ep[ep_order] = C_ep_PQ[j].push(node0); // put this ep into cluster j
				ep_order++;
			}

		}

		// for active cluster
		if (get(boost::vertex_name_t(), input_graph, i) > 0) {
			Active_C_num++; // the number of active clusters
			C_activity[i] = true; // this cluster is active
			C_event_time[i] = get(boost::vertex_name_t(), input_graph, i); // the event time is the node weight
			// push node into C_event_PQ
			node0.index = i; // node index: cluster order
			node0.priority_value = C_event_time[i]; // priority: node weight
			handle_Cevent[i] = C_event_PQ.push(node0); // into PQ
			// all the ep for cluster i have been inserted into C_ep_PQ[i]; Note that, it's only true when i starts from 0 and j>i above
			// push node into E_event_PQ
			node0.priority_value = C_ep_PQ[i].top().priority_value; // priority: the closest ep time
			handle_Eevent[i] = E_event_PQ.push(node0); // into PQ

			//cout << "C_ep_PQ[i].size():" << C_ep_PQ[i].size() << endl;
			//cout << "C_ep_PQ[i].top().priority_value:" << C_ep_PQ[i].top().priority_value << endl;
			//cout << "node0.priority_value:" << node0.priority_value << endl;
			//cout << "E_event_PQ.size():" << E_event_PQ.size() << endl;
			//cout << "E_event_PQ.top().priority_value:" << E_event_PQ.top().priority_value << endl;
			//getchar();
		}
	}


	// FGW growth starts!
	int C0, C1, C2, ep1, ep2;
	double Tc, Te, r, lowerbound = 1e-7;  // d is not used in this coding; it does not matter
	vector<pair<int, int>> merged_edges;
	pair<int, int> edge;

	while (Active_C_num > 1) // stop the loop when there is only 1 active clusters left
	{
		// find the closest event
		Tc = C_event_PQ.top().priority_value; // this cluster event time
		Te = E_event_PQ.top().priority_value; // this edge event time

		if (Tc >= Te) { // edge event

			C1 = E_event_PQ.top().index; // the cluster C1 for this edge event
			ep1 = C_ep_PQ[C1].top().index; // the top ep in C1
			C2 = V_locator[ep_v2_list[ep1]]; // the cluster C2 for this edge event

			if (C1 == C2) { // the inside ep is triggered
				C_ep_PQ[C1].pop(); // pop out the inside ep
				// decrease E_event_PQ for the change of event_C1
				node0.index = C1;
				node0.priority_value = C_ep_PQ[C1].top().priority_value; // theoretically C_ep_PQ[event_C1] should not be empty
				E_event_PQ.decrease(handle_Eevent[C1], node0);
			}
			else { // the outside ep is triggered
				Global_time = Te;
				ep2 = ep_ep2_order_list[ep1];

				if (C_activity[C2] == true) { // C2 is active
					r = ep_EventTime_list[ep2] - Global_time; // the slack of the responsible edge

					if (r > lowerbound) { // r is big; d is not used in this coding
						// change two ep event time
						ep_EventTime_list[ep1] = Global_time + r / 2;
						ep_EventTime_list[ep2] = Global_time + r / 2;
						// update C_ep_PQ in C1
						node0.index = ep1;
						node0.priority_value = ep_EventTime_list[ep1];
						C_ep_PQ[C1].decrease(handle_ep[ep1], node0);
						// update C_ep_PQ in C2
						node0.index = ep2;
						node0.priority_value = ep_EventTime_list[ep2];
						C_ep_PQ[C2].increase(handle_ep[ep2], node0);
						// update E_event_PQ for the change of C1
						node0.index = C1;
						node0.priority_value = C_ep_PQ[C1].top().priority_value;
						E_event_PQ.decrease(handle_Eevent[C1], node0);
						// update E_event_PQ for the change of C2
						if (C_ep_PQ[C2].top().index == ep2) {
							node0.index = C2;
							node0.priority_value = C_ep_PQ[C2].top().priority_value;
							E_event_PQ.increase(handle_Eevent[C2], node0);
						}
					}
					else { // r is small; merge event

						merged_edges.insert(merged_edges.end(), { ep_v1_list[ep1] ,ep_v1_list[ep2] }); // merge edge 

						// merge V_list of C2 into C1
						C_V_list[C1].insert(end(C_V_list[C1]), begin(C_V_list[C2]), end(C_V_list[C2]));
						//decrease V_locator
						for (int i = 0; i < C_V_list[C2].size(); i++) {
							V_locator[C_V_list[C2][i]] = C1;
						}
						// update event time of C1
						C_event_time[C1] = C_event_time[C1] + C_event_time[C2] - Global_time;
						// minus one active cluster
						Active_C_num--;
						C_activity[C2] = false;
						// merge two C_ep_PQ
						C_ep_PQ[C1].pop(); // pop out the responsible ep
						C_ep_PQ[C1].merge(C_ep_PQ[C2]);
						//fibonacci_heap<node>().swap(C_ep_PQ[C2]);
						// update C1 in C_event_time and E_event_time
						node0.index = C1;
						node0.priority_value = C_event_time[C1];
						C_event_PQ.decrease(handle_Cevent[C1], node0);
						node0.priority_value = C_ep_PQ[C1].top().priority_value;
						E_event_PQ.decrease(handle_Eevent[C1], node0);
						// remove C2 from C_event_time and E_event_time
						C_event_PQ.erase(handle_Cevent[C2]);
						E_event_PQ.erase(handle_Eevent[C2]);
					}
				}
				else { // C2 is inactive
					r = ep_EventTime_list[ep2] - C_event_time[C2]; // the slack of the responsible edge

					if (r > lowerbound) { // r is big; d is not used in this coding
						// change two ep event time
						ep_EventTime_list[ep1] = Global_time + r;
						ep_EventTime_list[ep2] = C_event_time[C2];
						// update C_ep_PQ in C1
						node0.index = ep1;
						node0.priority_value = ep_EventTime_list[ep1];
						C_ep_PQ[C1].decrease(handle_ep[ep1], node0);
						// update C_ep_PQ in C2
						node0.index = ep2;
						node0.priority_value = ep_EventTime_list[ep2];
						C_ep_PQ[C2].increase(handle_ep[ep2], node0);
						// update E_event_PQ for the change of C1
						node0.index = C1;
						node0.priority_value = C_ep_PQ[C1].top().priority_value;
						E_event_PQ.decrease(handle_Eevent[C1], node0);
					}
					else { // r is small; merge event

						merged_edges.insert(merged_edges.end(), { ep_v1_list[ep1] ,ep_v1_list[ep2] }); // merge edge 

						// merge V_list of C2 into C1
						C_V_list[C1].insert(end(C_V_list[C1]), begin(C_V_list[C2]), end(C_V_list[C2]));
						//decrease V_locator
						for (int i = 0; i < C_V_list[C2].size(); i++) {
							V_locator[C_V_list[C2][i]] = C1;
						}
						// merge two C_ep_PQ
						C_ep_PQ[C1].pop(); // pop out the responsible ep		   
						typename pairing_heap<node>::iterator begin = C_ep_PQ[C2].begin();
						typename pairing_heap<node>::iterator end = C_ep_PQ[C2].end();
						for (typename pairing_heap<node>::iterator it = begin; it != end; ++it)
						{
							node0 = *it;
							if (V_locator[ep_v2_list[node0.index]] != C1) { // only push outside nodes into C_ep_PQ[event_C1]; it's a little faster than not do that
								node0.priority_value = node0.priority_value + Global_time - C_event_time[C2]; // decrease priority values
								handle_ep[node0.index] = C_ep_PQ[C1].push(node0); // push; decrease handle
							}
						}

						// decrease C1 in E_event_time
						node0.index = C1;
						node0.priority_value = C_ep_PQ[C1].top().priority_value;
						E_event_PQ.decrease(handle_Eevent[C1], node0);
					}
				}
			}
		}
		else { // cluster event
			Global_time = Tc; // decrease time
			C0 = C_event_PQ.top().index; // the cluster for this cluster event
			Active_C_num--; // minus one active cluster
			C_event_PQ.pop(); // remove the cluster from C_event_PQ
			E_event_PQ.erase(handle_Eevent[C0]); // remove the cluster from E_event_PQ
			C_activity[C0] = false; // deactivate it
		}
	}



	// get maximal clusters
	vector<int>  maximal_clusters;
	vector<bool>  checked_maximal_cluster(N, false);
	for (int i = 0; i < N - 1; i++) { // there is a dummy vertex
		if (checked_maximal_cluster[V_locator[i]] == false) { // V_locator[i]: the maximal_cluster contains vertex i
			checked_maximal_cluster[V_locator[i]] = true;
			maximal_clusters.insert(maximal_clusters.end(), V_locator[i]); // a newly identified maximal_cluster
		}
	}


	// output solution_trees
	solution_trees.resize(maximal_clusters.size()); // solution_trees contain all maximal_clusters
	for (int i = 0; i < N - 1; i++) { // there is a dummy vertex
		for (int j = 0; j < maximal_clusters.size(); j++) {
			if (maximal_clusters[j] == V_locator[i]) { // vertex i is in maximal_clusters[j]
				solution_trees[j].first.insert(solution_trees[j].first.end(), i); // insert vertex i into solution_trees
				break;
			}
		}
	}
	for (int i = 0; i < merged_edges.size(); i++) {
		for (int j = 0; j < maximal_clusters.size(); j++) {
			if (maximal_clusters[j] == V_locator[merged_edges[i].first]) { // merged_edges[i] is in maximal_clusters[j]
				solution_trees[j].second.insert(solution_trees[j].second.end(), merged_edges[i]); // insert merged_edges[i]
				break;
			}
		}
	}


	return solution_trees;



}
#pragma endregion FGW_growth_forest_for_Concrete_Bumps  

#pragma region
vector<pair<vector<int>, vector<pair<int, int>>>> FGW_clustering_for_Concrete_Bumps(graph& input_graph) {

	/*input_graph may be disconnected; add dummy vertices and edges for disconnected input_graph;
	the reason to do this is that your FGW_growth_forest codes only suits graph where every vertex is connected by at least
	one edge, as otherwise the edge component of a singular vertex is empty, and the queue cannot pop out elements*/
	int N = num_vertices(input_graph); // number of vertices
	double M = 1e20; // we assume that M is large enough to guarantee that dummy components are not in FGW_trees
	boost::add_vertex(N, input_graph); // add a dummy vertex
	boost::put(boost::vertex_name_t(), input_graph, N, 0); // this dummy vertex has no prize and thus is inactive
	for (int i = 0; i < N; i++) {
		boost::add_edge(N, i, M, input_graph); // add dummy edges
	}


	/*generate FGW_trees*/
	vector<pair<vector<int>, vector<pair<int, int>>>> FGW_trees = FGW_growth_forest_for_Concrete_Bumps(input_graph, 2);


	/*remove dummy components from input_graph*/
	clear_vertex(N, input_graph);
	remove_vertex(N, input_graph);

	return FGW_trees;

}
#pragma endregion FGW_clustering_for_Concrete_Bumps

#pragma region
void push_trees_roots_into_Q_for_Concrete_Bumps(vector<pair<vector<int>, vector<pair<int, int>>>>& input_trees, 
	graph& input_trees_graph, graph& initial_graph,
	pairing_heap<node_max_heaps_int_index>& Queue) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;

	int N = num_vertices(initial_graph);

	/*initialize nw values, unprocessed, processing_degree*/
	vector<double> nw(N);
	vector<int> unprocessed(N), processing_degree(N);
	for (int i = 0; i < input_trees.size(); i++) {
		for (int j = 0; j < input_trees[i].first.size(); j++) {
			int v = input_trees[i].first[j];
			nw[v] = get(boost::vertex_name_t(), initial_graph, v); // initial nw values are prizes
			unprocessed[v] = 1; // all the vertices in trees are unprocessed initially
		}
		for (int j = 0; j < input_trees[i].second.size(); j++) {
			int v1 = input_trees[i].second[j].first;
			int v2 = input_trees[i].second[j].second;
			processing_degree[v1]++; /*initialize processing_degree*/
			processing_degree[v2]++;
		}
	}


	/*update nw values without root*/
	vector<int> target_vertex; // vertices which are unprocessed and have a processing_degree of 1
	for (int i = 0; i < input_trees.size(); i++) {
		for (int j = 0; j < input_trees[i].first.size(); j++) {
			int v = input_trees[i].first[j];
			if (processing_degree[v] == 1 && unprocessed[v] == 1) {
				target_vertex.insert(target_vertex.end(), v);
			}
		}
	}
	while (target_vertex.size() > 0) { // end the process until there is no target vertex any more
		int v = target_vertex[0]; // processing target_vertex[0]
		boost::tie(ai, a_end) = boost::adjacent_vertices(v, input_trees_graph); // adj vertices in input_trees_graph
		for (; ai != a_end; ai++) {
			if (unprocessed[*ai] == 1) { // *ai is unprocessed, so *ai is v_adj
				double ec = get(boost::edge_weight_t(), initial_graph, boost::edge(v, *ai, initial_graph).first);
				if (ec < nw[v]) {
					nw[*ai] = nw[*ai] + nw[v] - ec; // update nw[*ai]
				}
				unprocessed[v] = 0; // mark v as processed
				processing_degree[*ai]--; // update processing_degree[*ai]
				if (processing_degree[*ai] == 1) { // *ai becomes a new target_vertex
					target_vertex.insert(target_vertex.end(), *ai);
				}
				break; // there is at most one v_adj (finally, target_vertex[0] is the remaining unprocessed vertex)
			}
		}
		target_vertex.erase(target_vertex.begin()); // erase target_vertex[0]
	}


	/*push_trees_roots_into_Q*/
	node_max_heaps_int_index Queue_node;
	for (int i = 0; i < input_trees.size(); i++) {
		int root;
		double nw_root = -1;
		for (int j = 0; j < input_trees[i].first.size(); j++) {
			int v = input_trees[i].first[j];
			if (nw_root < nw[v]) {
				nw_root = nw[v];
				root = v;
			}
		}
		Queue_node.index = root;
		Queue_node.priority_value = nw_root;
		//Queue.push(Queue_node);
		//cout << "Hegde_2015 nw_root: " << nw_root << endl;
		if (nw_root > 0) {
			Queue.push(Queue_node);
		}

	}

}
#pragma endregion push_trees_roots_into_Q_for_Concrete_Bumps

#pragma region
void push_trees_roots_into_Q_subgraph_unordered_map_for_Concrete_Bumps
(vector<pair<vector<int>, vector<pair<int, int>>>>& input_trees,
	subgraph& input_trees_graph, graph& initial_graph,
	pairing_heap<node_max_heaps_int_index>& Queue) {

	/*initialize nw values, unprocessed, processing_degree*/
	unordered_map<int, double> nw;
	unordered_map<int, int> unprocessed, processing_degree;
	for (int i = 0; i < input_trees.size(); i++) {
		for (int j = 0; j < input_trees[i].first.size(); j++) {
			int v = input_trees[i].first[j];
			nw[v] = get(boost::vertex_name_t(), initial_graph, v); // initial nw values are prizes
			unprocessed[v] = 1; // all the vertices in trees are unprocessed initially
		}
		for (int j = 0; j < input_trees[i].second.size(); j++) {
			int v1 = input_trees[i].second[j].first;
			int v2 = input_trees[i].second[j].second;
			processing_degree[v1] = 0; /*initialize processing_degree*/
			processing_degree[v2] = 0;
		}
	}
	for (int i = 0; i < input_trees.size(); i++) {
		for (int j = 0; j < input_trees[i].second.size(); j++) {
			int v1 = input_trees[i].second[j].first;
			int v2 = input_trees[i].second[j].second;
			processing_degree[v1]++;
			processing_degree[v2]++;
		}
	}


	/*update nw values without root*/
	vector<int> target_vertex; // vertices which are unprocessed and have a processing_degree of 1
	for (int i = 0; i < input_trees.size(); i++) {
		for (int j = 0; j < input_trees[i].first.size(); j++) {
			int v = input_trees[i].first[j];
			if (processing_degree[v] == 1 && unprocessed[v] == 1) {
				target_vertex.insert(target_vertex.end(), v);
			}
		}
	}
	while (target_vertex.size() > 0) { // end the process until there is no target vertex any more
		int v = target_vertex[0]; // processing target_vertex[0]
		std::list<int> adj_vertices = subgraph_adjacent_vertices(input_trees_graph, v);
		for (std::list<int>::iterator it = adj_vertices.begin(); it != adj_vertices.end(); it++) {
			int adj_v = *it;
			if (unprocessed[adj_v] == 1) { // adj_v is unprocessed, so adj_v is v_adj
				double ec = get(boost::edge_weight_t(), initial_graph, boost::edge(v, adj_v, initial_graph).first);
				if (ec < nw[v]) {
					nw[adj_v] = nw[adj_v] + nw[v] - ec; // update nw[adj_v]
				}
				unprocessed[v] = 0; // mark v as processed
				processing_degree[adj_v]--; // update processing_degree[adj_v]
				if (processing_degree[adj_v] == 1) { // adj_v becomes a new target_vertex
					target_vertex.insert(target_vertex.end(), adj_v);
				}
				break; // there is at most one v_adj (finally, target_vertex[0] is the remaining unprocessed vertex)
			}
		}
		target_vertex.erase(target_vertex.begin()); // erase target_vertex[0]
	}

	/*push_trees_roots_into_Q*/
	node_max_heaps_int_index Queue_node;
	for (int i = 0; i < input_trees.size(); i++) {
		int root;
		double nw_root = -1;
		for (int j = 0; j < input_trees[i].first.size(); j++) {
			int v = input_trees[i].first[j];
			if (nw_root < nw[v]) {
				nw_root = nw[v];
				root = v;
			}
		}
		Queue_node.index = root;
		Queue_node.priority_value = nw_root;
		//Queue.push(Queue_node);
		//cout << "Hegde_2015 nw_root: " << nw_root << endl;
		if (nw_root > 0) {
			Queue.push(Queue_node);
		}

	}


	//cout << "push_trees_roots_into_Q_subgraph_unordered_map:" << endl;
	//subgraph_print(input_trees_graph);

}
#pragma endregion push_trees_roots_into_Q_subgraph_unordered_map_for_Concrete_Bumps

#pragma region
int ABHA_subgraph_unordered_map_for_Concrete_Bumps(graph& initial_graph,
	vector<pair<vector<int>, vector<pair<int, int>>>> input_trees) {

	/*input_trees is changed below; so, do not make &input_trees*/

	/*time complexity: O(k|V|)*/

	vector<pair<vector<int>, vector<pair<int, int>>>> solution_trees;
	int N = num_vertices(initial_graph);

	/*build input_trees_graph*/
	subgraph input_trees_graph = build_trees_graph_subgraph_unordered_map(input_trees);

	/*a max priority queue*/
	pairing_heap<node_max_heaps_int_index> Queue;

	/*push roots of input_trees into Queue*/
	push_trees_roots_into_Q_subgraph_unordered_map_for_Concrete_Bumps(input_trees, input_trees_graph, initial_graph, Queue);


	/*hunting bumps*/
	//auto begin = std::chrono::high_resolution_clock::now();
	while (Queue.size() > 0) {
		// end it when solution_trees.size() = target_k or Queue.size() = 0


		//cout << "print_forest(input_trees):" << endl;
		//print_forest(input_trees);
		//cout << "print_forest(solution_trees):" << endl;
		//print_forest(solution_trees);
		//cout << "solution_trees.size(): " << solution_trees.size() << endl;
		//cout << "Queue.size(): " << Queue.size() << endl;

		/*dequeue*/
		int v_top = Queue.top().index;
		double v_top_priority = Queue.top().priority_value;
		//cout << "ABHA add Queue.top().priority_value: " << Queue.top().priority_value << endl;
		Queue.pop();

		//cout << endl;
		//cout << "v_top:" << v_top << endl;
		//cout << "v_top_priority:" << v_top_priority << endl;
		//getchar();
		//cout << endl;

		/*add a bump with v_top as the root; input_trees and input_trees_graph are updated*/
		vector<pair<vector<int>, vector<pair<int, int>>>> new_trees; // the new trees due to the removal of the bump from input_trees
		//auto begin1 = std::chrono::high_resolution_clock::now();
		add_a_bump_with_root_subgraph_unordered_map(input_trees, input_trees_graph, initial_graph, v_top, solution_trees, new_trees);
		//cout << "solution_trees.size(): " << solution_trees.size() << endl;
		//auto end1 = std::chrono::high_resolution_clock::now();
		//double runningtime1 = std::chrono::duration_cast<std::chrono::nanoseconds>(end1 - begin1).count() / 1e9; // s
		//cout << "add_a_bump_with_root runningtime: " << runningtime1 << endl;

		//cout << "print_forest(new_trees):" << endl;
		//print_forest(new_trees);

		/*push roots of new_trees into Queue*/
		//auto begin2 = std::chrono::high_resolution_clock::now();
		push_trees_roots_into_Q_subgraph_unordered_map_for_Concrete_Bumps(new_trees, input_trees_graph, initial_graph, Queue);
		//auto end2 = std::chrono::high_resolution_clock::now();
		//double runningtime2 = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
		//cout << "push_trees_roots_into_Q runningtime: " << runningtime2 << endl;

		//cout << "print_forest(input_trees):" << endl;
		//print_forest(input_trees);
		//cout << "print_forest(solution_trees):" << endl;
		//print_forest(solution_trees);
		//cout << "solution_trees.size(): " << solution_trees.size() << endl;
		//cout << "Queue.size(): " << Queue.size() << endl;
		//cout << endl;

	}
	//auto end = std::chrono::high_resolution_clock::now();
	//double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
	//cout << "hunting bumps runningtime: " << runningtime << endl;

	//cout << "print_forest(input_trees):" << endl;
	//print_forest(input_trees);
	//cout << "print_forest(solution_trees):" << endl;
	//print_forest(solution_trees);
	//cout << "solution_trees.size(): " << solution_trees.size() << endl;
	//cout << "Queue.size(): " << Queue.size() << endl;


	return solution_trees.size();


}
#pragma endregion ABHA_subgraph_unordered_map_for_Concrete_Bumps

#pragma region
vector<pair<vector<int>, vector<pair<int, int>>>> ABHA_subgraph_unordered_map_for_Concrete_Bumps_size(graph& initial_graph,
	vector<pair<vector<int>, vector<pair<int, int>>>> input_trees) {

	/*input_trees is changed below; so, do not make &input_trees*/

	/*time complexity: O(k|V|)*/

	vector<pair<vector<int>, vector<pair<int, int>>>> solution_trees;
	int N = num_vertices(initial_graph);

	/*build input_trees_graph*/
	subgraph input_trees_graph = build_trees_graph_subgraph_unordered_map(input_trees);

	/*a max priority queue*/
	pairing_heap<node_max_heaps_int_index> Queue;

	/*push roots of input_trees into Queue*/
	push_trees_roots_into_Q_subgraph_unordered_map_for_Concrete_Bumps(input_trees, input_trees_graph, initial_graph, Queue);


	/*hunting bumps*/
	//auto begin = std::chrono::high_resolution_clock::now();
	while (Queue.size() > 0) {
		// end it when solution_trees.size() = target_k or Queue.size() = 0


		//cout << "print_forest(input_trees):" << endl;
		//print_forest(input_trees);
		//cout << "print_forest(solution_trees):" << endl;
		//print_forest(solution_trees);
		//cout << "solution_trees.size(): " << solution_trees.size() << endl;
		//cout << "Queue.size(): " << Queue.size() << endl;

		/*dequeue*/
		int v_top = Queue.top().index;
		double v_top_priority = Queue.top().priority_value;
		//cout << "ABHA add Queue.top().priority_value: " << Queue.top().priority_value << endl;
		Queue.pop();

		//cout << endl;
		//cout << "v_top:" << v_top << endl;
		//cout << "v_top_priority:" << v_top_priority << endl;
		//getchar();
		//cout << endl;

		/*add a bump with v_top as the root; input_trees and input_trees_graph are updated*/
		vector<pair<vector<int>, vector<pair<int, int>>>> new_trees; // the new trees due to the removal of the bump from input_trees
		//auto begin1 = std::chrono::high_resolution_clock::now();
		add_a_bump_with_root_subgraph_unordered_map(input_trees, input_trees_graph, initial_graph, v_top, solution_trees, new_trees);
		//cout << "solution_trees.size(): " << solution_trees.size() << endl;
		//auto end1 = std::chrono::high_resolution_clock::now();
		//double runningtime1 = std::chrono::duration_cast<std::chrono::nanoseconds>(end1 - begin1).count() / 1e9; // s
		//cout << "add_a_bump_with_root runningtime: " << runningtime1 << endl;

		//cout << "print_forest(new_trees):" << endl;
		//print_forest(new_trees);

		/*push roots of new_trees into Queue*/
		//auto begin2 = std::chrono::high_resolution_clock::now();
		push_trees_roots_into_Q_subgraph_unordered_map_for_Concrete_Bumps(new_trees, input_trees_graph, initial_graph, Queue);
		//auto end2 = std::chrono::high_resolution_clock::now();
		//double runningtime2 = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
		//cout << "push_trees_roots_into_Q runningtime: " << runningtime2 << endl;

		//cout << "print_forest(input_trees):" << endl;
		//print_forest(input_trees);
		//cout << "print_forest(solution_trees):" << endl;
		//print_forest(solution_trees);
		//cout << "solution_trees.size(): " << solution_trees.size() << endl;
		//cout << "Queue.size(): " << Queue.size() << endl;
		//cout << endl;

	}
	//auto end = std::chrono::high_resolution_clock::now();
	//double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
	//cout << "hunting bumps runningtime: " << runningtime << endl;

	//cout << "print_forest(input_trees):" << endl;
	//print_forest(input_trees);
	//cout << "print_forest(solution_trees):" << endl;
	//print_forest(solution_trees);
	//cout << "solution_trees.size(): " << solution_trees.size() << endl;
	//cout << "Queue.size(): " << Queue.size() << endl;


	return solution_trees;


}
#pragma endregion ABHA_subgraph_unordered_map_for_Concrete_Bumps_size

#pragma region
int number_of_Concrete_Bumps(graph& input_graph) {

	auto begin1 = std::chrono::high_resolution_clock::now();
	vector<pair<vector<int>, vector<pair<int, int>>>> FGW_trees = FGW_clustering_for_Concrete_Bumps(input_graph);
	auto end1 = std::chrono::high_resolution_clock::now();
	double runningtime1 = std::chrono::duration_cast<std::chrono::nanoseconds>(end1 - begin1).count() / 1e9; // s
	cout << "FGW_trees_time: " << runningtime1 << "s" << endl;

	auto begin2 = std::chrono::high_resolution_clock::now();
	int num = ABHA_subgraph_unordered_map_for_Concrete_Bumps(input_graph, FGW_trees);
	auto end2 = std::chrono::high_resolution_clock::now();
	double runningtime2 = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
	cout << "ABHA_for_Concrete_Bumps_time: " << runningtime2 << "s" << endl;

	return num;

}
#pragma endregion number_of_Concrete_Bumps

#pragma region
vector<pair<vector<int>, vector<pair<int, int>>>> size_of_Concrete_Bumps(graph& input_graph) {

	vector<pair<vector<int>, vector<pair<int, int>>>> FGW_trees = FGW_clustering_for_Concrete_Bumps(input_graph);

	return ABHA_subgraph_unordered_map_for_Concrete_Bumps_size(input_graph, FGW_trees);

}
#pragma endregion size_of_Concrete_Bumps

#pragma region
void size_of_Concrete_Bumps_statistics_DBLP() {

	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);

	/*input DBLP graphs*/
	graph DBLP_graph, DBLP_group_graph;
	std::vector<string> DBLP_expert_names, DBLP_skill_names;
	read_DBLP_data(DBLP_graph, DBLP_group_graph, DBLP_expert_names, DBLP_skill_names);
	boost_graph_ec_update_pairwise_jaccard_distance(DBLP_graph);


	double alpha = 1, beta = 1;
	int DBLP_N = num_vertices(DBLP_graph), DBLP_skill_N = DBLP_skill_names.size(),
		iteration_times = 20;
	outputFile.open("size_of_Concrete_Bumps_statistics_DBLP.csv"); // stp file
	outputFile << "size" << endl;
	for (int i = 0; i < iteration_times; i++) {
		int skill_num = 30;
		std::vector<bool> query_nodes;
		graph DBLP_instance = generate_DBLP_instance(DBLP_graph, DBLP_group_graph, skill_num, query_nodes, alpha, beta);

		vector<pair<vector<int>, vector<pair<int, int>>>> bumps = size_of_Concrete_Bumps(DBLP_instance);
		for (int j = 0; j < bumps.size(); j++) {
			outputFile << bumps[j].first.size() << endl;
		}
	}
	outputFile.close();



}
#pragma endregion size_of_Concrete_Bumps_statistics_DBLP

#pragma region
void size_of_Concrete_Bumps_statistics_Twitter() {

	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);

	/*input Twitter and Flickr graphs*/
	graph Twitter_graph_base;
	std::vector<double> Twitter_prizes, Flickr_prizes;
	std::vector<pair<double, double>> locations;
	read_Austin_graph(Twitter_graph_base, Twitter_prizes, Flickr_prizes, locations);

	double alpha = 1, beta = 1;

	/*Twitter_statistics*/
	outputFile.open("size_of_Concrete_Bumps_statistics_Twitter.csv");
	outputFile << "size" << endl;
	double prize_bound = 10;

	std::vector<bool> query_nodes;
	graph DBLP_instance = generate_Twitter_instance(Twitter_graph_base, Twitter_prizes, prize_bound, query_nodes, alpha, beta);

	vector<pair<vector<int>, vector<pair<int, int>>>> bumps = size_of_Concrete_Bumps(DBLP_instance);
	for (int j = 0; j < bumps.size(); j++) {
		outputFile << bumps[j].first.size() << endl;
	}
	outputFile.close();


}
#pragma endregion size_of_Concrete_Bumps_statistics_Twitter

#pragma region
void number_of_Concrete_Bumps_Twitter_special() {

	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);

	/*input Twitter and Flickr graphs*/
	graph Twitter_graph_base;
	std::vector<double> Twitter_prizes, Flickr_prizes;
	std::vector<pair<double, double>> locations;
	read_Austin_graph(Twitter_graph_base, Twitter_prizes, Flickr_prizes, locations);

	double alpha = 1, beta = 0.5;


	/*Twitter_statistics*/
	double max_prize = 0;
	for (int i = 0; i < Twitter_prizes.size(); i++) {
		if (Twitter_prizes[i] > max_prize) {
			max_prize = Twitter_prizes[i];
		}
	}
	double prize_bound = 10;
	std::vector<bool> query_nodes;
	graph DBLP_instance = generate_Twitter_instance(Twitter_graph_base,
		Twitter_prizes, prize_bound, query_nodes, alpha, beta);
	cout << "number_of_Concrete_Bumps(DBLP_instance): " << 
		number_of_Concrete_Bumps(DBLP_instance) << endl;



}
#pragma endregion number_of_Concrete_Bumps_Twitter_special

#pragma region
void single_skill_Q_DBLP_large() {

	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);

	/*input DBLP graphs*/
	graph DBLP_graph, DBLP_group_graph;
	std::vector<string> DBLP_expert_names, DBLP_skill_names;
	read_DBLP_data(DBLP_graph, DBLP_group_graph, DBLP_expert_names, DBLP_skill_names);
	boost_graph_ec_update_pairwise_jaccard_distance(DBLP_graph);
	int input_N = num_vertices(DBLP_graph), input_skill_N = num_vertices(DBLP_group_graph) - input_N;
	/*DBLP_statistics*/
	outputFile.open("single_skill_Q_DBLP_large.csv"); // stp file
	outputFile << "queryed_num" << endl;
	for (int i = 0; i < input_skill_N; i++) {
		outputFile << in_degree(input_N + i, DBLP_group_graph) << endl;
	}
	outputFile.close();



}
#pragma endregion single_skill_Q_DBLP_large

#pragma region
void pre_experiments_statistics_large_DBLP() {

	double alpha = 1, beta = 1;

	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);

	/*input DBLP graphs*/
	graph DBLP_graph, DBLP_group_graph;
	std::vector<string> DBLP_expert_names, DBLP_skill_names;
	read_DBLP_data(DBLP_graph, DBLP_group_graph, DBLP_expert_names, DBLP_skill_names);
	boost_graph_ec_update_pairwise_jaccard_distance(DBLP_graph);
	/*DBLP_statistics*/
	int DBLP_N = num_vertices(DBLP_graph), DBLP_skill_N = DBLP_skill_names.size(),
		iteration_times = 1000, skill_num_min = 1, skill_num_max = 30;
	outputFile.open("pre_experiments_statistics_DBLP.csv"); // stp file
	outputFile << "skill_num,queryed_num,number_of_Concrete_Bumps" << endl;
	for (int i = 0; i < iteration_times; i++) {
		cout << "DBLP_statistics: " << i << endl;
		int skill_num = skill_num_min + (rand() % (int)(skill_num_max - skill_num_min + 1));
		std::vector<bool> query_nodes;
		graph DBLP_instance = generate_DBLP_instance(DBLP_graph, DBLP_group_graph, skill_num, query_nodes, alpha, beta);
		int queryed_num = std::accumulate(query_nodes.begin(), query_nodes.end(), 0); // sum of vector
		outputFile << skill_num << "," << queryed_num << "," << number_of_Concrete_Bumps(DBLP_instance) << endl;
	}
	outputFile.close();


}
#pragma endregion pre_experiments_statistics_large_DBLP

#pragma region
void pre_experiments_statistics_Twitter() {

	double alpha = 1, beta = 1;
	int iteration_times = 1000;

	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);


	/*input Twitter and Flickr graphs*/
	graph Twitter_graph_base;
	std::vector<double> Twitter_prizes, Flickr_prizes;
	std::vector<pair<double, double>> locations;
	read_Austin_graph(Twitter_graph_base, Twitter_prizes, Flickr_prizes, locations);

	/*Twitter_statistics*/
	double max_prize = 0;
	for (int i = 0; i < Twitter_prizes.size(); i++) {
		if (Twitter_prizes[i] > max_prize) {
			max_prize = Twitter_prizes[i];
		}
	}
	double min = 10, max = 50;
	outputFile.open("pre_experiments_statistics_Twitter.csv");
	outputFile << "prize_bound,queryed_num,number_of_Concrete_Bumps" << endl;
	for (int i = 10; i < iteration_times + 1; i++) {
		double prize_bound = min + (double)i * (max - min) / iteration_times;

		std::vector<bool> query_nodes;
		graph DBLP_instance = generate_Twitter_instance(Twitter_graph_base, Twitter_prizes, prize_bound, query_nodes, alpha, beta);

		int queryed_num = std::accumulate(query_nodes.begin(), query_nodes.end(), 0); // sum of vector

		outputFile << prize_bound << "," << queryed_num << "," << number_of_Concrete_Bumps(DBLP_instance) << endl;
	}
	outputFile.close();


}
#pragma endregion pre_experiments_statistics_Twitter




// Experiments

#pragma region
void experiment_Vary_V_DBLP_large(string name, graph& DBLP_graph, graph& DBLP_group_graph, 
	int V_min, int V_max, double alpha, double beta,
	int queried_skills_num, int iteration_times, int k) {

	std::time_t now = std::time(0);
	boost::random::mt19937 gen{ static_cast<std::uint32_t>(now) };
	boost::random::uniform_int_distribution<> dist{ V_min, V_max };

	/*change k DBLP*/
	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);

	outputFile.open(name); // stp file
	outputFile << "V,algorithm,solution,runningtime" << endl;
	for (int iteration = 0; iteration < iteration_times; iteration++) {

		cout << "experiment_Vary_V_DBLP_large iteration: " << iteration << endl;

		//auto begin0 = std::chrono::high_resolution_clock::now();

		int V = dist(gen);

		//cout << "V=" << V << endl;

		graph DBLP_instance;
		std::vector<bool> query_nodes;

		if (V == num_vertices(DBLP_graph)) {
			DBLP_instance = generate_DBLP_instance(DBLP_graph, DBLP_group_graph, queried_skills_num, query_nodes, alpha, beta);
		}
		else {
			/*generate small instance*/
			DBLP_instance = generate_smaller_DBLP_instance(DBLP_graph, DBLP_group_graph, V, queried_skills_num, query_nodes, alpha, beta);
		}

		//int queryed_num = std::accumulate(query_nodes.begin(), query_nodes.end(), 0); // sum of vector
		//cout << "queryed_num: " << queryed_num << endl; 


		auto begin3 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> FGW_trees = FGW_clustering(DBLP_instance, k);
		auto end3 = std::chrono::high_resolution_clock::now();
		double runningtime3 = std::chrono::duration_cast<std::chrono::nanoseconds>(end3 - begin3).count() / 1e9; // s


		auto begin4 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_GBHA = GBHA(DBLP_instance, k, FGW_trees);
		auto end4 = std::chrono::high_resolution_clock::now();
		double runningtime4 = runningtime3 + std::chrono::duration_cast<std::chrono::nanoseconds>(end4 - begin4).count() / 1e9; // s
		double nw_solutions_GBHA = forest_net_weight(DBLP_instance, solutions_GBHA);


		auto begin5 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_Hegde_2015 = Hegde_2015(DBLP_instance, k, FGW_trees);
		auto end5 = std::chrono::high_resolution_clock::now();
		double runningtime5 = runningtime3 + std::chrono::duration_cast<std::chrono::nanoseconds>(end5 - begin5).count() / 1e9; // s
		double nw_solutions_Hegde_2015 = forest_net_weight(DBLP_instance, solutions_Hegde_2015);

		outputFile << V << ",Our GBHA," << nw_solutions_GBHA << "," << runningtime4 << endl;
		outputFile << V << ",Hegde et al.'s FGWA," << nw_solutions_Hegde_2015 << "," << runningtime5 << endl;

		//auto end0 = std::chrono::high_resolution_clock::now();
		//double runningtime0 = std::chrono::duration_cast<std::chrono::nanoseconds>(end0 - begin0).count() / 1e9; // s
		//cout << "experiment_Vary_V_DBLP_large iteration time: " << runningtime0 << "s" << endl;


	}
	outputFile.close();


}
#pragma endregion experiment_Vary_V_DBLP_large

#pragma region
void experiment_Vary_k_DBLP_large(string name, graph& DBLP_graph, graph& DBLP_group_graph, 
	double alpha, double beta, int queried_skills_num,
	int iteration_times, int k_min, int k_max) {

	std::time_t now = std::time(0);
	boost::random::mt19937 gen{ static_cast<std::uint32_t>(now) };
	boost::random::uniform_int_distribution<> dist{ k_min, k_max };

	/*change k DBLP*/
	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);

	outputFile.open(name); // stp file
	outputFile << "random_k,algorithm,solution,runningtime" << endl;
	for (int iteration = 0; iteration < iteration_times; iteration++) {

		cout << "experiment_Vary_k_DBLP_large iteration: " << iteration << endl;

		int random_k = dist(gen);

		std::vector<bool> query_nodes;
		graph DBLP_instance;

		DBLP_instance = generate_DBLP_instance(DBLP_graph, DBLP_group_graph,
			queried_skills_num, query_nodes, alpha, beta);

		auto begin3 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> FGW_trees = FGW_clustering(DBLP_instance, random_k);
		auto end3 = std::chrono::high_resolution_clock::now();
		double runningtime3 = std::chrono::duration_cast<std::chrono::nanoseconds>(end3 - begin3).count() / 1e9; // s


		auto begin4 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_GBHA = GBHA(DBLP_instance, random_k, FGW_trees);
		auto end4 = std::chrono::high_resolution_clock::now();
		double runningtime4 = runningtime3 + std::chrono::duration_cast<std::chrono::nanoseconds>(end4 - begin4).count() / 1e9; // s
		double nw_solutions_GBHA = forest_net_weight(DBLP_instance, solutions_GBHA);


		auto begin5 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_Hegde_2015 = Hegde_2015(DBLP_instance, random_k, FGW_trees);
		auto end5 = std::chrono::high_resolution_clock::now();
		double runningtime5 = runningtime3 + std::chrono::duration_cast<std::chrono::nanoseconds>(end5 - begin5).count() / 1e9; // s
		double nw_solutions_Hegde_2015 = forest_net_weight(DBLP_instance, solutions_Hegde_2015);

		outputFile << random_k << ",Our GBHA," << nw_solutions_GBHA << "," << runningtime4 << endl;
		outputFile << random_k << ",Hegde et al.'s FGWA," << nw_solutions_Hegde_2015 << "," << runningtime5 << endl;

	}
	outputFile.close();


}
#pragma endregion experiment_Vary_k_DBLP_large

#pragma region
void experiment_Vary_Q_DBLP_large(string name, graph& DBLP_graph, graph& DBLP_group_graph, double alpha, double beta,
	int queried_skills_num_min, int queried_skills_num_max, int iteration_times, int k) {

	std::time_t now = std::time(0);
	boost::random::mt19937 gen{ static_cast<std::uint32_t>(now) };
	boost::random::uniform_int_distribution<> dist{ queried_skills_num_min, queried_skills_num_max };

	/*change k DBLP*/
	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);

	outputFile.open(name); // stp file
	outputFile << "Q,algorithm,solution,runningtime" << endl;
	for (int iteration = 0; iteration < iteration_times; iteration++) {

		cout << "experiment_Vary_Q_DBLP_large iteration: " << iteration << endl;

		//int queried_skills_num = queried_skills_num_min + (rand() % (int)(queried_skills_num_max - queried_skills_num_min + 1));
		int queried_skills_num = dist(gen);

		graph DBLP_instance;
		std::vector<bool> query_nodes;

		DBLP_instance = generate_DBLP_instance(DBLP_graph, DBLP_group_graph,
			queried_skills_num, query_nodes, alpha, beta);

		int queryed_num = std::accumulate(query_nodes.begin(), query_nodes.end(), 0); // sum of vector

		auto begin3 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> FGW_trees = FGW_clustering(DBLP_instance, k);
		auto end3 = std::chrono::high_resolution_clock::now();
		double runningtime3 = std::chrono::duration_cast<std::chrono::nanoseconds>(end3 - begin3).count() / 1e9; // s

		auto begin4 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_GBHA = GBHA(DBLP_instance, k, FGW_trees);
		auto end4 = std::chrono::high_resolution_clock::now();
		double runningtime4 = runningtime3 + std::chrono::duration_cast<std::chrono::nanoseconds>(end4 - begin4).count() / 1e9; // s
		double nw_solutions_GBHA = forest_net_weight(DBLP_instance, solutions_GBHA);


		auto begin5 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_Hegde_2015 = Hegde_2015(DBLP_instance, k, FGW_trees);
		auto end5 = std::chrono::high_resolution_clock::now();
		double runningtime5 = runningtime3 + std::chrono::duration_cast<std::chrono::nanoseconds>(end5 - begin5).count() / 1e9; // s
		double nw_solutions_Hegde_2015 = forest_net_weight(DBLP_instance, solutions_Hegde_2015);

		outputFile << queryed_num << ",Our GBHA," << nw_solutions_GBHA << "," << runningtime4 << endl;
		outputFile << queryed_num << ",Hegde et al.'s FGWA," << nw_solutions_Hegde_2015 << "," << runningtime5 << endl;

	}
	outputFile.close();


}
#pragma endregion experiment_Vary_Q_DBLP_large

#pragma region
void experiment_Vary_alpha_DBLP_large(string name, graph& DBLP_graph, graph& DBLP_group_graph, 
	double alpha_min, double alpha_max, double beta,
	int queried_skills_num, int iteration_times, int k) {


	double aaa = 1e8;

	std::time_t now = std::time(0);
	boost::random::mt19937 gen{ static_cast<std::uint32_t>(now) };
	boost::random::uniform_int_distribution<> dist{ (int)(alpha_min * aaa), (int)(alpha_max * aaa) };

	/*change k DBLP*/
	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);

	outputFile.open(name); // stp file
	outputFile << "alpha,algorithm,solution,runningtime" << endl;
	for (int iteration = 0; iteration < iteration_times; iteration++) {

		cout << "experiment_Vary_alpha_DBLP_large iteration: " << iteration << endl;

		double alpha = (double)dist(gen) / aaa;

		graph DBLP_instance;
		std::vector<bool> query_nodes;

		DBLP_instance = generate_DBLP_instance(DBLP_graph,
			DBLP_group_graph, queried_skills_num, query_nodes, alpha, beta);


		//int queryed_num = std::accumulate(query_nodes.begin(), query_nodes.end(), 0); // sum of vector

		auto begin3 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> FGW_trees = FGW_clustering(DBLP_instance, k);
		auto end3 = std::chrono::high_resolution_clock::now();
		double runningtime3 = std::chrono::duration_cast<std::chrono::nanoseconds>(end3 - begin3).count() / 1e9; // s


		auto begin4 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_GBHA = GBHA(DBLP_instance, k, FGW_trees);
		auto end4 = std::chrono::high_resolution_clock::now();
		double runningtime4 = runningtime3 + std::chrono::duration_cast<std::chrono::nanoseconds>(end4 - begin4).count() / 1e9; // s
		double nw_solutions_GBHA = forest_net_weight(DBLP_instance, solutions_GBHA);


		auto begin5 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_Hegde_2015 = Hegde_2015(DBLP_instance, k, FGW_trees);
		auto end5 = std::chrono::high_resolution_clock::now();
		double runningtime5 = runningtime3 + std::chrono::duration_cast<std::chrono::nanoseconds>(end5 - begin5).count() / 1e9; // s
		double nw_solutions_Hegde_2015 = forest_net_weight(DBLP_instance, solutions_Hegde_2015);

		outputFile << alpha << ",Our GBHA," << nw_solutions_GBHA << "," << runningtime4 << endl;
		outputFile << alpha << ",Hegde et al.'s FGWA," << nw_solutions_Hegde_2015 << "," << runningtime5 << endl;

	}
	outputFile.close();


}
#pragma endregion experiment_Vary_alpha_DBLP_large

#pragma region
void experiment_Vary_beta_DBLP_large(string name, graph& DBLP_graph, graph& DBLP_group_graph, 
	double alpha, double beta_min, double beta_max,
	int queried_skills_num, int iteration_times, int k) {

	double aaa = 1e8;

	std::time_t now = std::time(0);
	boost::random::mt19937 gen{ static_cast<std::uint32_t>(now) };
	boost::random::uniform_int_distribution<> dist{ (int)(beta_min * aaa), (int)(beta_max * aaa) };

	/*change k DBLP*/
	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);

	outputFile.open(name); // stp file
	outputFile << "beta,algorithm,solution,runningtime" << endl;
	for (int iteration = 0; iteration < iteration_times; iteration++) {

		cout << "experiment_Vary_beta_DBLP_large iteration: " << iteration << endl;

		double beta = (double)dist(gen) / aaa;


		graph DBLP_instance;
		std::vector<bool> query_nodes;

		DBLP_instance = generate_DBLP_instance(DBLP_graph,
			DBLP_group_graph, queried_skills_num, query_nodes, alpha, beta);

		auto begin3 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> FGW_trees = FGW_clustering(DBLP_instance, k);
		auto end3 = std::chrono::high_resolution_clock::now();
		double runningtime3 = std::chrono::duration_cast<std::chrono::nanoseconds>(end3 - begin3).count() / 1e9; // s

		auto begin4 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_GBHA = GBHA(DBLP_instance, k, FGW_trees);
		auto end4 = std::chrono::high_resolution_clock::now();
		double runningtime4 = runningtime3 + std::chrono::duration_cast<std::chrono::nanoseconds>(end4 - begin4).count() / 1e9; // s
		double nw_solutions_GBHA = forest_net_weight(DBLP_instance, solutions_GBHA);


		auto begin5 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_Hegde_2015 = Hegde_2015(DBLP_instance, k, FGW_trees);
		auto end5 = std::chrono::high_resolution_clock::now();
		double runningtime5 = runningtime3 + std::chrono::duration_cast<std::chrono::nanoseconds>(end5 - begin5).count() / 1e9; // s
		double nw_solutions_Hegde_2015 = forest_net_weight(DBLP_instance, solutions_Hegde_2015);

		outputFile << beta << ",Our GBHA," << nw_solutions_GBHA << "," << runningtime4 << endl;
		outputFile << beta << ",Hegde et al.'s FGWA," << nw_solutions_Hegde_2015 << "," << runningtime5 << endl;

	}
	outputFile.close();


}
#pragma endregion experiment_Vary_beta_DBLP_large

#pragma region
void experiment_Vary_V_Twitter(string name, graph& Twitter_graph_base, 
	std::vector<double>& Twitter_prizes, 
	int V_min, int V_max, double alpha, double beta, double prize_LB, int iteration_times, int k,
	int random_ST_try, int root_query_node_num) {





	std::time_t now = std::time(0);
	boost::random::mt19937 gen{ static_cast<std::uint32_t>(now) };
	boost::random::uniform_int_distribution<> dist{ V_min, V_max };

	/*change k DBLP*/
	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);

	outputFile.open(name); // stp file
	outputFile << "V,algorithm,solution,runningtime" << endl;
	for (int iteration = 0; iteration < iteration_times; iteration++) {

		//int V = V_min + (rand() % (int)(V_max - V_min + 1));
		int V = dist(gen);

		graph DBLP_instance;
		std::vector<bool> query_nodes;

		if (V == num_vertices(Twitter_graph_base)) {
			DBLP_instance = generate_Twitter_instance(Twitter_graph_base, Twitter_prizes, prize_LB, query_nodes, alpha, beta);
		}
		else {
			/*generate small instance*/
			DBLP_instance = generate_smaller_Twitter_instance(Twitter_graph_base, Twitter_prizes, V, prize_LB, query_nodes,
				alpha, beta);
		}

		auto begin0 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_adapted_BF_ST = adapted_BF_ST
		(DBLP_instance, query_nodes, k, root_query_node_num);
		auto end0 = std::chrono::high_resolution_clock::now();
		double runningtime0 = std::chrono::duration_cast<std::chrono::nanoseconds>(end0 - begin0).count() / 1e9; // s
		double nw_solutions_adapted_BF_ST = forest_net_weight(DBLP_instance, solutions_adapted_BF_ST);

		auto begin1 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_adapted_random_ST =
			adapted_random_ST(DBLP_instance, k, random_ST_try);
		auto end1 = std::chrono::high_resolution_clock::now();
		double runningtime1 = std::chrono::duration_cast<std::chrono::nanoseconds>(end1 - begin1).count() / 1e9; // s
		double nw_solutions_adapted_random_ST = forest_net_weight(DBLP_instance, solutions_adapted_random_ST);


		auto begin2 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_adapted_smart_ST = 
			adapted_smart_ST(DBLP_instance, query_nodes, k);
		auto end2 = std::chrono::high_resolution_clock::now();
		double runningtime2 = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
		double nw_solutions_adapted_smart_ST = forest_net_weight(DBLP_instance, solutions_adapted_smart_ST);


		auto begin3 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> FGW_trees = FGW_clustering(DBLP_instance, k);
		auto end3 = std::chrono::high_resolution_clock::now();
		double runningtime3 = std::chrono::duration_cast<std::chrono::nanoseconds>(end3 - begin3).count() / 1e9; // s



		//cout << "FGW_trees.size(): " << FGW_trees.size() << endl;
		//getchar();


		auto begin4 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_GBHA = GBHA(DBLP_instance, k, FGW_trees);
		auto end4 = std::chrono::high_resolution_clock::now();
		double runningtime4 = runningtime3 + std::chrono::duration_cast<std::chrono::nanoseconds>(end4 - begin4).count() / 1e9; // s
		double nw_solutions_GBHA = forest_net_weight(DBLP_instance, solutions_GBHA);


		auto begin5 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_Hegde_2015 = Hegde_2015(DBLP_instance, k, FGW_trees);
		auto end5 = std::chrono::high_resolution_clock::now();
		double runningtime5 = runningtime3 + std::chrono::duration_cast<std::chrono::nanoseconds>(end5 - begin5).count() / 1e9; // s
		double nw_solutions_Hegde_2015 = forest_net_weight(DBLP_instance, solutions_Hegde_2015);

		//print_forest_with_weights(solutions_Hegde_2015, DBLP_instance);
		outputFile << V << ",Our BF-ST," << nw_solutions_adapted_BF_ST << "," << runningtime0 << endl;
		outputFile << V << ",Our Random-ST," << nw_solutions_adapted_random_ST << "," << runningtime1 << endl;
		outputFile << V << ",Our Smart-ST," << nw_solutions_adapted_smart_ST << "," << runningtime2 << endl;
		outputFile << V << ",Our GBHA," << nw_solutions_GBHA << "," << runningtime4 << endl;
		outputFile << V << ",Hegde et al.'s FGWA," << nw_solutions_Hegde_2015 << "," << runningtime5 << endl;


		//cout << "check now random_k=" << random_k << endl;
		//getchar();
	}
	outputFile.close();


}
#pragma endregion experiment_Vary_V_Twitter

#pragma region
void experiment_Vary_k_Twitter(string name, graph& Twitter_graph_base, std::vector<double>& Twitter_prizes, double alpha, double beta
, double prize_LB, int iteration_times, int k_min, int k_max,
int random_ST_try, int root_query_node_num) {


	std::time_t now = std::time(0);
	boost::random::mt19937 gen{ static_cast<std::uint32_t>(now) };
	boost::random::uniform_int_distribution<> dist{ k_min, k_max };

	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);

	outputFile.open(name); // stp file
	outputFile << "random_k,algorithm,solution,runningtime" << endl;
	for (int iteration = 0; iteration < iteration_times; iteration++) {

		std::vector<bool> query_nodes;
		graph Twitter_instance = generate_Twitter_instance(Twitter_graph_base, Twitter_prizes, prize_LB, query_nodes, alpha, beta);

		//int random_k = k_min + (rand() % (int)(k_max - k_min + 1));
		int random_k = dist(gen);

		auto begin0 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_adapted_BF_ST = adapted_BF_ST
		(Twitter_instance, query_nodes, random_k, root_query_node_num);
		auto end0 = std::chrono::high_resolution_clock::now();
		double runningtime0 = std::chrono::duration_cast<std::chrono::nanoseconds>(end0 - begin0).count() / 1e9; // s
		double nw_solutions_adapted_BF_ST = forest_net_weight(Twitter_instance, solutions_adapted_BF_ST);

		auto begin1 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_adapted_random_ST =
			adapted_random_ST(Twitter_instance, random_k, random_ST_try);
		auto end1 = std::chrono::high_resolution_clock::now();
		double runningtime1 = std::chrono::duration_cast<std::chrono::nanoseconds>(end1 - begin1).count() / 1e9; // s
		double nw_solutions_adapted_random_ST = forest_net_weight(Twitter_instance, solutions_adapted_random_ST);


		auto begin2 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_adapted_smart_ST = adapted_smart_ST(Twitter_instance, query_nodes, random_k);
		auto end2 = std::chrono::high_resolution_clock::now();
		double runningtime2 = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
		double nw_solutions_adapted_smart_ST = forest_net_weight(Twitter_instance, solutions_adapted_smart_ST);


		auto begin3 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> FGW_trees = FGW_clustering(Twitter_instance, random_k);
		auto end3 = std::chrono::high_resolution_clock::now();
		double runningtime3 = std::chrono::duration_cast<std::chrono::nanoseconds>(end3 - begin3).count() / 1e9; // s



		//cout << "FGW_trees.size(): " << FGW_trees.size() << endl;
		//getchar();


		auto begin4 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_GBHA = GBHA(Twitter_instance, random_k, FGW_trees);
		auto end4 = std::chrono::high_resolution_clock::now();
		double runningtime4 = runningtime3 + std::chrono::duration_cast<std::chrono::nanoseconds>(end4 - begin4).count() / 1e9; // s
		double nw_solutions_GBHA = forest_net_weight(Twitter_instance, solutions_GBHA);


		auto begin5 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_Hegde_2015 = Hegde_2015(Twitter_instance, random_k, FGW_trees);
		auto end5 = std::chrono::high_resolution_clock::now();
		double runningtime5 = runningtime3 + std::chrono::duration_cast<std::chrono::nanoseconds>(end5 - begin5).count() / 1e9; // s
		double nw_solutions_Hegde_2015 = forest_net_weight(Twitter_instance, solutions_Hegde_2015);

		//print_forest_with_weights(solutions_Hegde_2015, DBLP_instance);

		outputFile << random_k << ",Our BF-ST," << nw_solutions_adapted_BF_ST << "," << runningtime0 << endl;
		outputFile << random_k << ",Our Random-ST," << nw_solutions_adapted_random_ST << "," << runningtime1 << endl;
		outputFile << random_k << ",Our Smart-ST," << nw_solutions_adapted_smart_ST << "," << runningtime2 << endl;
		outputFile << random_k << ",Our GBHA," << nw_solutions_GBHA << "," << runningtime4 << endl;
		outputFile << random_k << ",Hegde et al.'s FGWA," << nw_solutions_Hegde_2015 << "," << runningtime5 << endl;

		//cout << "check now random_k=" << random_k << endl;
		//getchar();
	}
	outputFile.close();


}
#pragma endregion experiment_Vary_k_Twitter

#pragma region
void experiment_Vary_Q_Twitter(string name, graph& Twitter_graph_base, std::vector<double>& Twitter_prizes, double alpha, double beta,
	int prize_LB_min, int prize_LB_max, int iteration_times, int k,
	int random_ST_try, int root_query_node_num) {


	std::time_t now = std::time(0);
	boost::random::mt19937 gen{ static_cast<std::uint32_t>(now) };
	boost::random::uniform_int_distribution<> dist{ prize_LB_min, prize_LB_max };

	/*change k DBLP*/
	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);

	outputFile.open(name); // stp file
	outputFile << "Q,algorithm,solution,runningtime" << endl;
	for (int iteration = 0; iteration < iteration_times; iteration++) {

		//double prize_LB = prize_LB_min + (rand() % (int)(prize_LB_max - prize_LB_min + 1));
		double prize_LB = dist(gen);


		std::vector<bool> query_nodes;
		graph DBLP_instance = generate_Twitter_instance(Twitter_graph_base, Twitter_prizes, prize_LB, query_nodes, alpha, beta);

		int queryed_num = std::accumulate(query_nodes.begin(), query_nodes.end(), 0); // sum of vector

		auto begin0 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_adapted_BF_ST = adapted_BF_ST
		(DBLP_instance, query_nodes, k, root_query_node_num);
		auto end0 = std::chrono::high_resolution_clock::now();
		double runningtime0 = std::chrono::duration_cast<std::chrono::nanoseconds>(end0 - begin0).count() / 1e9; // s
		double nw_solutions_adapted_BF_ST = forest_net_weight(DBLP_instance, solutions_adapted_BF_ST);

		auto begin1 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_adapted_random_ST =
			adapted_random_ST(DBLP_instance, k, random_ST_try);
		auto end1 = std::chrono::high_resolution_clock::now();
		double runningtime1 = std::chrono::duration_cast<std::chrono::nanoseconds>(end1 - begin1).count() / 1e9; // s
		double nw_solutions_adapted_random_ST = forest_net_weight(DBLP_instance, solutions_adapted_random_ST);

		auto begin2 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_adapted_smart_ST = adapted_smart_ST(DBLP_instance, query_nodes, k);
		auto end2 = std::chrono::high_resolution_clock::now();
		double runningtime2 = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
		double nw_solutions_adapted_smart_ST = forest_net_weight(DBLP_instance, solutions_adapted_smart_ST);


		auto begin3 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> FGW_trees = FGW_clustering(DBLP_instance, k);
		auto end3 = std::chrono::high_resolution_clock::now();
		double runningtime3 = std::chrono::duration_cast<std::chrono::nanoseconds>(end3 - begin3).count() / 1e9; // s



		//cout << "FGW_trees.size(): " << FGW_trees.size() << endl;
		//getchar();


		auto begin4 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_GBHA = GBHA(DBLP_instance, k, FGW_trees);
		auto end4 = std::chrono::high_resolution_clock::now();
		double runningtime4 = runningtime3 + std::chrono::duration_cast<std::chrono::nanoseconds>(end4 - begin4).count() / 1e9; // s
		double nw_solutions_GBHA = forest_net_weight(DBLP_instance, solutions_GBHA);


		auto begin5 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_Hegde_2015 = Hegde_2015(DBLP_instance, k, FGW_trees);
		auto end5 = std::chrono::high_resolution_clock::now();
		double runningtime5 = runningtime3 + std::chrono::duration_cast<std::chrono::nanoseconds>(end5 - begin5).count() / 1e9; // s
		double nw_solutions_Hegde_2015 = forest_net_weight(DBLP_instance, solutions_Hegde_2015);

		//print_forest_with_weights(solutions_Hegde_2015, DBLP_instance);

		outputFile << queryed_num << ",Our BF-ST," << nw_solutions_adapted_BF_ST << "," << runningtime0 << endl;
		outputFile << queryed_num << ",Our Random-ST," << nw_solutions_adapted_random_ST << "," << runningtime1 << endl;
		outputFile << queryed_num << ",Our Smart-ST," << nw_solutions_adapted_smart_ST << "," << runningtime2 << endl;
		outputFile << queryed_num << ",Our GBHA," << nw_solutions_GBHA << "," << runningtime4 << endl;
		outputFile << queryed_num << ",Hegde et al.'s FGWA," << nw_solutions_Hegde_2015 << "," << runningtime5 << endl;


		//cout << "check now random_k=" << random_k << endl;
		//getchar();
	}
	outputFile.close();


}
#pragma endregion experiment_Vary_Q_Twitter

#pragma region
void experiment_Vary_alpha_Twitter(string name, graph& Twitter_graph_base, std::vector<double>& Twitter_prizes, 
	double alpha_min, double alpha_max, double beta,
	double prize_LB, int iteration_times, int k,
	int random_ST_try, int root_query_node_num) {

	double aaa = 1e8;

	std::time_t now = std::time(0);
	boost::random::mt19937 gen{ static_cast<std::uint32_t>(now) };
	boost::random::uniform_int_distribution<> dist{ (int)(alpha_min * aaa), (int)(alpha_max * aaa) };

	/*change k DBLP*/
	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);

	outputFile.open(name); // stp file
	outputFile << "alpha,algorithm,solution,runningtime" << endl;
	for (int iteration = 0; iteration < iteration_times; iteration++) {

		double alpha = (double)dist(gen) / aaa;

		std::vector<bool> query_nodes;
		graph DBLP_instance = generate_Twitter_instance(Twitter_graph_base, Twitter_prizes, prize_LB, query_nodes, alpha, beta);

		int queryed_num = std::accumulate(query_nodes.begin(), query_nodes.end(), 0); // sum of vector

		auto begin0 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_adapted_BF_ST = adapted_BF_ST
		(DBLP_instance, query_nodes, k, root_query_node_num);
		auto end0 = std::chrono::high_resolution_clock::now();
		double runningtime0 = std::chrono::duration_cast<std::chrono::nanoseconds>(end0 - begin0).count() / 1e9; // s
		double nw_solutions_adapted_BF_ST = forest_net_weight(DBLP_instance, solutions_adapted_BF_ST);

		auto begin1 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_adapted_random_ST =
			adapted_random_ST(DBLP_instance, k, random_ST_try);
		auto end1 = std::chrono::high_resolution_clock::now();
		double runningtime1 = std::chrono::duration_cast<std::chrono::nanoseconds>(end1 - begin1).count() / 1e9; // s
		double nw_solutions_adapted_random_ST = forest_net_weight(DBLP_instance, solutions_adapted_random_ST);

		auto begin2 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_adapted_smart_ST = adapted_smart_ST(DBLP_instance, query_nodes, k);
		auto end2 = std::chrono::high_resolution_clock::now();
		double runningtime2 = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
		double nw_solutions_adapted_smart_ST = forest_net_weight(DBLP_instance, solutions_adapted_smart_ST);


		auto begin3 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> FGW_trees = FGW_clustering(DBLP_instance, k);
		auto end3 = std::chrono::high_resolution_clock::now();
		double runningtime3 = std::chrono::duration_cast<std::chrono::nanoseconds>(end3 - begin3).count() / 1e9; // s



		//cout << "FGW_trees.size(): " << FGW_trees.size() << endl;
		//getchar();


		auto begin4 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_GBHA = GBHA(DBLP_instance, k, FGW_trees);
		auto end4 = std::chrono::high_resolution_clock::now();
		double runningtime4 = runningtime3 + std::chrono::duration_cast<std::chrono::nanoseconds>(end4 - begin4).count() / 1e9; // s
		double nw_solutions_GBHA = forest_net_weight(DBLP_instance, solutions_GBHA);


		auto begin5 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_Hegde_2015 = Hegde_2015(DBLP_instance, k, FGW_trees);
		auto end5 = std::chrono::high_resolution_clock::now();
		double runningtime5 = runningtime3 + std::chrono::duration_cast<std::chrono::nanoseconds>(end5 - begin5).count() / 1e9; // s
		double nw_solutions_Hegde_2015 = forest_net_weight(DBLP_instance, solutions_Hegde_2015);

		//print_forest_with_weights(solutions_Hegde_2015, DBLP_instance);

		outputFile << alpha << ",Our BF-ST," << nw_solutions_adapted_BF_ST << "," << runningtime0 << endl;
		outputFile << alpha << ",Our Random-ST," << nw_solutions_adapted_random_ST << "," << runningtime1 << endl;
		outputFile << alpha << ",Our Smart-ST," << nw_solutions_adapted_smart_ST << "," << runningtime2 << endl;
		outputFile << alpha << ",Our GBHA," << nw_solutions_GBHA << "," << runningtime4 << endl;
		outputFile << alpha << ",Hegde et al.'s FGWA," << nw_solutions_Hegde_2015 << "," << runningtime5 << endl;


		//cout << "check now random_k=" << random_k << endl;
		//getchar();
	}
	outputFile.close();


}
#pragma endregion experiment_Vary_alpha_Twitter

#pragma region
void experiment_Vary_beta_Twitter(string name, graph& Twitter_graph_base, std::vector<double>& Twitter_prizes,
	double alpha, double beta_min, double beta_max,
	double prize_LB, int iteration_times, int k,
	int random_ST_try, int root_query_node_num) {


	/*change k DBLP*/
	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);

	outputFile.open(name); // stp file
	outputFile << "beta,algorithm,solution,runningtime" << endl;
	for (int iteration = 0; iteration < iteration_times; iteration++) {

		double aaa = 1e2;
		double beta = (double) beta_min * aaa + (rand() % (int)(beta_max* aaa - beta_min * aaa + 1));
		beta = beta / aaa;


		std::vector<bool> query_nodes;
		graph DBLP_instance = generate_Twitter_instance(Twitter_graph_base, Twitter_prizes, prize_LB, query_nodes, alpha, beta);

		int queryed_num = std::accumulate(query_nodes.begin(), query_nodes.end(), 0); // sum of vector

		auto begin0 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_adapted_BF_ST = adapted_BF_ST
		(DBLP_instance, query_nodes, k, root_query_node_num);
		auto end0 = std::chrono::high_resolution_clock::now();
		double runningtime0 = std::chrono::duration_cast<std::chrono::nanoseconds>(end0 - begin0).count() / 1e9; // s
		double nw_solutions_adapted_BF_ST = forest_net_weight(DBLP_instance, solutions_adapted_BF_ST);

		auto begin1 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_adapted_random_ST =
			adapted_random_ST(DBLP_instance, k, random_ST_try);
		auto end1 = std::chrono::high_resolution_clock::now();
		double runningtime1 = std::chrono::duration_cast<std::chrono::nanoseconds>(end1 - begin1).count() / 1e9; // s
		double nw_solutions_adapted_random_ST = forest_net_weight(DBLP_instance, solutions_adapted_random_ST);

		auto begin2 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_adapted_smart_ST = adapted_smart_ST(DBLP_instance, query_nodes, k);
		auto end2 = std::chrono::high_resolution_clock::now();
		double runningtime2 = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
		double nw_solutions_adapted_smart_ST = forest_net_weight(DBLP_instance, solutions_adapted_smart_ST);


		auto begin3 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> FGW_trees = FGW_clustering(DBLP_instance, k);
		auto end3 = std::chrono::high_resolution_clock::now();
		double runningtime3 = std::chrono::duration_cast<std::chrono::nanoseconds>(end3 - begin3).count() / 1e9; // s



		//cout << "FGW_trees.size(): " << FGW_trees.size() << endl;
		//getchar();


		auto begin4 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_GBHA = GBHA(DBLP_instance, k, FGW_trees);
		auto end4 = std::chrono::high_resolution_clock::now();
		double runningtime4 = runningtime3 + std::chrono::duration_cast<std::chrono::nanoseconds>(end4 - begin4).count() / 1e9; // s
		double nw_solutions_GBHA = forest_net_weight(DBLP_instance, solutions_GBHA);


		auto begin5 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_Hegde_2015 = Hegde_2015(DBLP_instance, k, FGW_trees);
		auto end5 = std::chrono::high_resolution_clock::now();
		double runningtime5 = runningtime3 + std::chrono::duration_cast<std::chrono::nanoseconds>(end5 - begin5).count() / 1e9; // s
		double nw_solutions_Hegde_2015 = forest_net_weight(DBLP_instance, solutions_Hegde_2015);

		//print_forest_with_weights(solutions_Hegde_2015, DBLP_instance);

		outputFile << beta << ",Our BF-ST," << nw_solutions_adapted_BF_ST << "," << runningtime0 << endl;
		outputFile << beta << ",Our Random-ST," << nw_solutions_adapted_random_ST << "," << runningtime1 << endl;
		outputFile << beta << ",Our Smart-ST," << nw_solutions_adapted_smart_ST << "," << runningtime2 << endl;
		outputFile << beta << ",Our GBHA," << nw_solutions_GBHA << "," << runningtime4 << endl;
		outputFile << beta << ",Hegde et al.'s FGWA," << nw_solutions_Hegde_2015 << "," << runningtime5 << endl;


		//cout << "check now random_k=" << random_k << endl;
		//getchar();
	}
	outputFile.close();


}
#pragma endregion experiment_Vary_beta_Twitter

#pragma region
void Twitter_experiment_part(string name, int iteration_times, int random_ST_try, int root_query_node_num) {

	/*input Twitter and Flickr graphs*/
	graph Twitter_graph_base;
	std::vector<double> Twitter_prizes, Flickr_prizes;
	std::vector<pair<double, double>> locations;
	read_Austin_graph(Twitter_graph_base, Twitter_prizes, Flickr_prizes, locations);


	double alpha = 1, beta = 1, prize_LB = 10;
	int k = 100; // queried_skills_num cannot be large in small graphs
	int k_min = 100, k_max = 150;
	double prize_LB_min = 10, prize_LB_max = 20; // you cannot set prize_LB_min = 0, as otherwise all the nodes are queried
	double alpha_min = 1, alpha_max = 1.1;
	double beta_min = 0, beta_max = 1;



	if (!name.compare("Vary_V_Twitter.csv")) {

		cout << "Run experiment_Vary_V_Twitter" << endl;

		experiment_Vary_V_Twitter(name, Twitter_graph_base, Twitter_prizes,
			60000, num_vertices(Twitter_graph_base), alpha, beta, prize_LB, iteration_times, k,
			random_ST_try, root_query_node_num);

		cout << "End experiment_Vary_V_Twitter" << endl;

	}
	else if (!name.compare("Vary_k_Twitter.csv")) {

		cout << "Run experiment_Vary_k_Twitter" << endl;

		experiment_Vary_k_Twitter(name, Twitter_graph_base, Twitter_prizes,
			alpha, beta, prize_LB, iteration_times, k_min, k_max, random_ST_try, root_query_node_num);

		cout << "End experiment_Vary_k_Twitter" << endl;

	}
	else if (!name.compare("Vary_Q_Twitter.csv")) {

		cout << "Run experiment_Vary_Q_Twitter" << endl;

		experiment_Vary_Q_Twitter(name, Twitter_graph_base, Twitter_prizes,
			alpha, beta, prize_LB_min, prize_LB_max, iteration_times, k, random_ST_try, root_query_node_num);

		cout << "End experiment_Vary_Q_Twitter" << endl;

	}
	else if (!name.compare("Vary_alpha_Twitter.csv")) {

		cout << "Run experiment_Vary_alpha_Twitter" << endl;

		experiment_Vary_alpha_Twitter(name, Twitter_graph_base, Twitter_prizes,
			alpha_min, alpha_max, beta, prize_LB, iteration_times, k, random_ST_try, root_query_node_num);

		cout << "End experiment_Vary_alpha_Twitter" << endl;
	}
	else if (!name.compare("Vary_beta_Twitter.csv")) {

		cout << "Run experiment_Vary_beta_Twitter" << endl;

		experiment_Vary_beta_Twitter(name, Twitter_graph_base, Twitter_prizes,
			alpha, beta_min, beta_max, prize_LB, iteration_times, k, random_ST_try, root_query_node_num);

		cout << "End experiment_Vary_beta_Twitter" << endl;
	}





}
#pragma endregion Twitter_experiment_part

#pragma region
void DBLP_large_experiment_part(string name, int iteration_times) {

	/*input DBLP graphs*/
	graph DBLP_graph, DBLP_group_graph;
	std::vector<string> DBLP_expert_names, DBLP_skill_names;
	read_DBLP_data(DBLP_graph, DBLP_group_graph, DBLP_expert_names, DBLP_skill_names);
	boost_graph_ec_update_pairwise_jaccard_distance(DBLP_graph);


	double alpha = 1, beta = 1;
	int queried_skills_num = 30, k = 150; // queried_skills_num cannot be large in small graphs
	int k_min = 150, k_max = 200;
    int queried_skills_num_min = 30, queried_skills_num_max = 30;
	double alpha_min = 1, alpha_max = 1.1;
	double beta_min = 0.9, beta_max = 1;



	if (!name.compare("Vary_V_DBLP.csv")) {
		cout << "Run experiment_Vary_V_DBLP" << endl;
		experiment_Vary_V_DBLP_large(name, DBLP_graph, DBLP_group_graph, 750000,
			num_vertices(DBLP_graph), alpha, beta, queried_skills_num, iteration_times, k);
		cout << "End experiment_Vary_V_DBLP" << endl;
	}
	else if (!name.compare("Vary_k_DBLP.csv")) {
		cout << "Run experiment_Vary_k_DBLP" << endl;
		experiment_Vary_k_DBLP_large(name, DBLP_graph, DBLP_group_graph, alpha, beta,
			queried_skills_num, iteration_times, k_min, k_max);
		cout << "End experiment_Vary_k_DBLP" << endl;

	}
	else if (!name.compare("Vary_Q_DBLP.csv")) {
		cout << "Run experiment_Vary_Q_DBLP" << endl;
		experiment_Vary_Q_DBLP_large(name, DBLP_graph, DBLP_group_graph,
			alpha, beta, queried_skills_num_min, queried_skills_num_max, iteration_times, k);
		cout << "End experiment_Vary_Q_DBLP" << endl;

	}
	else if (!name.compare("Vary_alpha_DBLP.csv")) {
		cout << "Run experiment_Vary_alpha_DBLP" << endl;
		experiment_Vary_alpha_DBLP_large(name, DBLP_graph, DBLP_group_graph, alpha_min, alpha_max, beta,
			queried_skills_num, iteration_times, k);
		cout << "End experiment_Vary_alpha_DBLP" << endl;
	}
	else if (!name.compare("Vary_beta_DBLP.csv")) {
		cout << "Run experiment_Vary_beta_DBLP" << endl;
		experiment_Vary_beta_DBLP_large(name, DBLP_graph, DBLP_group_graph, alpha, beta_min, beta_max,
			queried_skills_num, iteration_times, k);
		cout << "End experiment_Vary_beta_DBLP" << endl;
	}





}
#pragma endregion DBLP_large_experiment_part

#pragma region
void experiments() {

	

	std::vector<string> name;
	int iteration_times = 4000;
	int random_ST_try = 10;
	int root_query_node_num = 10;



	int Twitter_try =1;
	int DBLP_try = 0;




	if (Twitter_try == 1) {	

		/*parallel*/
		//name.insert(name.end(), "Vary_V_Twitter.csv");
		//name.insert(name.end(), "Vary_k_Twitter.csv");
		//name.insert(name.end(), "Vary_Q_Twitter.csv");
		//name.insert(name.end(), "Vary_alpha_Twitter.csv");
		//name.insert(name.end(), "Vary_beta_Twitter.csv");
		//boost::thread_group threads;
		//for (int i = 0; i < name.size(); i++) {
		//	boost::thread* t1 = new boost::thread{ Twitter_experiment_part, name[i],iteration_times,
		//random_ST_try , root_query_node_num };
		//	threads.add_thread(t1);
		//}
		//threads.join_all();

		Twitter_experiment_part("Vary_V_Twitter.csv", iteration_times, random_ST_try, root_query_node_num);
		//Twitter_experiment_part("Vary_k_Twitter.csv", iteration_times, random_ST_try, root_query_node_num);
		//Twitter_experiment_part("Vary_Q_Twitter.csv", iteration_times, random_ST_try, root_query_node_num);
		//Twitter_experiment_part("Vary_alpha_Twitter.csv", iteration_times, random_ST_try, root_query_node_num);
		//Twitter_experiment_part("Vary_beta_Twitter.csv", iteration_times, random_ST_try, root_query_node_num);

	}

	
	if (DBLP_try == 1) {

		///*parallel*/
		//name.insert(name.end(), "Vary_V_DBLP.csv");
		//name.insert(name.end(), "Vary_k_DBLP.csv");
		//name.insert(name.end(), "Vary_Q_DBLP.csv");
		//name.insert(name.end(), "Vary_alpha_DBLP.csv");
		//name.insert(name.end(), "Vary_beta_DBLP.csv");
		//boost::thread_group threads;
		//for (int i = 0; i < name.size(); i++) {
		//	boost::thread* t1 = new boost::thread{ DBLP_large_experiment_part, name[i],iteration_times};
		//	threads.add_thread(t1);
		//}
		//threads.join_all();

		DBLP_large_experiment_part("Vary_V_DBLP.csv", iteration_times);
		//DBLP_large_experiment_part("Vary_k_DBLP.csv", iteration_times);
		//DBLP_large_experiment_part("Vary_Q_DBLP.csv", iteration_times);
		//DBLP_large_experiment_part("Vary_alpha_DBLP.csv", iteration_times);
		//DBLP_large_experiment_part("Vary_beta_DBLP.csv", iteration_times);


	}







}
#pragma endregion experiments

#pragma region
void compare_solutions() {

	std::vector<string> data_names = { "DBLP", "Twitter" };

	for (int i = 0; i < data_names.size(); i++) {

		cout << data_names[i] << endl;

		std::vector<std::vector<string>> contents;
		std::vector<std::vector<string>> contents1 = read_csv("Vary_V_" + data_names[i] + ".csv");
		std::vector<std::vector<string>> contents2 = read_csv("Vary_Q_" + data_names[i] + ".csv");
		std::vector<std::vector<string>> contents3 = read_csv("Vary_k_" + data_names[i] + ".csv");
		std::vector<std::vector<string>> contents4 = read_csv("Vary_alpha_" + data_names[i] + ".csv");
		std::vector<std::vector<string>> contents5 = read_csv("Vary_beta_" + data_names[i] + ".csv");

		contents.insert(contents.end(), contents1.begin(), contents1.end());
		contents.insert(contents.end(), contents2.begin(), contents2.end());
		contents.insert(contents.end(), contents3.begin(), contents3.end());
		contents.insert(contents.end(), contents4.begin(), contents4.end());
		contents.insert(contents.end(), contents5.begin(), contents5.end());

		double GWA_solu = 0, GBHA_solu = 0, Smart_solu = 0, BF_solu = 0, Random_solu = 0;

		for (int j = 0; j < contents.size(); j++) {
			if (!contents[j][1].compare("Our Smart-ST")) {
				Smart_solu = Smart_solu + stod(contents[j][2]);
			}
			else if (!contents[j][1].compare("Our BF-ST")) {
				BF_solu = BF_solu + stod(contents[j][2]);
			}
			else if (!contents[j][1].compare("Our Random-ST")) {
				Random_solu = Random_solu + stod(contents[j][2]);
			}
			else if (!contents[j][1].compare("Our GBHA")) {
				GBHA_solu = GBHA_solu + stod(contents[j][2]);
			}
			else if (!contents[j][1].compare("Hegde et al.'s FGWA")) {
				GWA_solu = GWA_solu + stod(contents[j][2]);
			}
		}

		cout << "GWA_solu: 100%	GBHA_solu: " << GBHA_solu / GWA_solu * 100
			<< "%	Smart_solu: " << Smart_solu / GWA_solu * 100
			<< "%	BF_solu: " << BF_solu / GWA_solu * 100
			<< "%	Random_solu: " << Random_solu / GWA_solu * 100
			<< "%" << endl;


	}


}
#pragma endregion compare_solutions







// compare original and adapted bump hunting algorithms

#pragma region
void original_vs_adapted() {

	/*input Twitter and Flickr graphs*/
	graph Twitter_graph_base;
	std::vector<double> Twitter_prizes, Flickr_prizes;
	std::vector<pair<double, double>> locations;
	read_Austin_graph(Twitter_graph_base, Twitter_prizes, Flickr_prizes, locations);

	int iteration_times = 2000;
	int V_min = 15000, V_max = 20000;
	double alpha = 1, beta = 1, prize_LB = 10;
	int k = 100; // queried_skills_num cannot be large in small graphs


	int random_ST_try = 10, root_query_node_num = 10;

	std::time_t now = std::time(0);
	boost::random::mt19937 gen{ static_cast<std::uint32_t>(now) };
	boost::random::uniform_int_distribution<> dist{ V_min, V_max };

	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);

	outputFile.open("original_vs_adapted.csv"); // stp file
	outputFile << "V,algorithm,solution,runningtime" << endl;
	for (int iteration = 0; iteration < iteration_times; iteration++) {

		cout << "original_vs_adapted iteration " << iteration << endl;

		//int V = V_min + (rand() % (int)(V_max - V_min + 1));
		int V = dist(gen);

		graph input_graph;
		std::vector<bool> query_nodes;

		if (V == num_vertices(Twitter_graph_base)) {
			input_graph = generate_Twitter_instance(Twitter_graph_base, Twitter_prizes, prize_LB, query_nodes, alpha, beta);
		}
		else {
			/*generate small instance*/
			input_graph = generate_smaller_Twitter_instance(Twitter_graph_base, Twitter_prizes, V, prize_LB, query_nodes,
				alpha, beta);
		}



		/*test adapted_random_ST*/
		auto begin1 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_adapted_random_ST =
			adapted_random_ST(input_graph, k, random_ST_try);
		auto end1 = std::chrono::high_resolution_clock::now();
		double runningtime1 = std::chrono::duration_cast<std::chrono::nanoseconds>(end1 - begin1).count() / 1e9; // s
		if (!are_these_k_independent_trees(input_graph, solutions_adapted_random_ST, k)) {
			cout << "Error: solutions_adapted_random_ST is not a feasible tree!" << endl;
			getchar();
			exit(1);
		}
		double nw_solutions_adapted_random_ST = forest_net_weight(input_graph, solutions_adapted_random_ST);

		/*test original_random_ST*/
		auto begin2 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_original_random_ST =
			original_random_ST(input_graph, k, random_ST_try);
		auto end2 = std::chrono::high_resolution_clock::now();
		double runningtime2 = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
		if (!are_these_k_independent_trees(input_graph, solutions_original_random_ST, k)) {
			cout << "solutions_original_random_ST contains null!" << endl;
			//getchar();
			//exit(1);
		}
		double nw_solutions_original_random_ST = forest_net_weight(input_graph, solutions_original_random_ST);

		/*test adapted_smart_ST*/
		auto begin3 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_adapted_smart_ST =
			adapted_smart_ST(input_graph, query_nodes, k);
		auto end3 = std::chrono::high_resolution_clock::now();
		double runningtime3 = std::chrono::duration_cast<std::chrono::nanoseconds>(end3 - begin3).count() / 1e9; // s
		if (!are_these_k_independent_trees(input_graph, solutions_adapted_smart_ST, k)) {
			cout << "Error: solutions_adapted_smart_ST is not a feasible tree!" << endl;
			getchar();
			exit(1);
		}
		double nw_solutions_adapted_smart_ST = forest_net_weight(input_graph, solutions_adapted_smart_ST);

		/*test original_smart_ST*/
		auto begin4 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_original_smart_ST =
			original_smart_ST(input_graph, query_nodes, k);
		auto end4 = std::chrono::high_resolution_clock::now();
		double runningtime4 = std::chrono::duration_cast<std::chrono::nanoseconds>(end4 - begin4).count() / 1e9; // s
		if (!are_these_k_independent_trees(input_graph, solutions_original_smart_ST, k)) {
			cout << "solutions_original_smart_ST contains null!" << endl;
			//getchar();
			//exit(1);
		}
		double nw_solutions_original_smart_ST = forest_net_weight(input_graph, solutions_original_smart_ST);


		/*test adapted_BF_ST*/
		auto begin5 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_adapted_BF_ST = adapted_BF_ST
		(input_graph, query_nodes, k, root_query_node_num);
		auto end5 = std::chrono::high_resolution_clock::now();
		double runningtime5 = std::chrono::duration_cast<std::chrono::nanoseconds>(end5 - begin5).count() / 1e9; // s
		if (!are_these_k_independent_trees(input_graph, solutions_adapted_BF_ST, k)) {
			cout << "Error: solutions_adapted_BF_ST is not a feasible tree!" << endl;
			getchar();
			exit(1);
		}
		double nw_solutions_adapted_BF_ST = forest_net_weight(input_graph, solutions_adapted_BF_ST);

		/*test original_BF_ST*/
		auto begin6 = std::chrono::high_resolution_clock::now();
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_original_BF_ST = original_BF_ST
		(input_graph, query_nodes, k, root_query_node_num);
		auto end6 = std::chrono::high_resolution_clock::now();
		double runningtime6 = std::chrono::duration_cast<std::chrono::nanoseconds>(end6 - begin6).count() / 1e9; // s
		if (!are_these_k_independent_trees(input_graph, solutions_original_BF_ST, k)) {
			cout << "solutions_original_BF_ST contains null!" << endl;
			//getchar();
			//exit(1);
		}
		double nw_solutions_original_BF_ST = forest_net_weight(input_graph, solutions_original_BF_ST);



		outputFile << V << ",adapted_random_ST," << nw_solutions_adapted_random_ST << "," << runningtime1 << endl;
		outputFile << V << ",original_random_ST," << nw_solutions_original_random_ST << "," << runningtime2 << endl;
		outputFile << V << ",adapted_smart_ST," << nw_solutions_adapted_smart_ST << "," << runningtime3 << endl;
		outputFile << V << ",original_smart_ST," << nw_solutions_original_smart_ST << "," << runningtime4 << endl;
		outputFile << V << ",adapted_BF_ST," << nw_solutions_adapted_BF_ST << "," << runningtime5 << endl;
		outputFile << V << ",original_BF_ST," << nw_solutions_original_BF_ST << "," << runningtime6 << endl;


	}
	outputFile.close();


}
#pragma endregion original_vs_adapted


// FastNewman2004 and FastVincent2008

#pragma region
struct node_FastNewman2004 {
	pair<int, int> index; // <community1,community2>
	double priority_value;
}; // define the node in the queue
bool operator<(node_FastNewman2004 const& x, node_FastNewman2004 const& y) {
	return x.priority_value < y.priority_value; // < is the max-heap; > is the min heap; PriorityQueue is expected to be a max-heap of integer values
} // redefine the operator since there are multiple values in each node
typedef typename pairing_heap<node_FastNewman2004>::handle_type handle_t_FastNewman2004; // define the handle type for pairing_heap<node>
#pragma endregion define heaps_FastNewman2004  

#pragma region
std::vector<int> FastNewman2004(graph& initial_graph) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;

	int N = num_vertices(initial_graph), E = num_edges(initial_graph);

	std::vector<std::vector<int>> communities(N);
	std::vector<int> vetex_2_communityID(N);
	/*every node is a community initially*/
	for (int i = 0; i < N; i++) {
		vetex_2_communityID[i] = i;
		communities[i].insert(communities[i].end(), i);
	}

	/*an adjacency list to store e_ij: one-half of the fraction of edges in the
	network that connect vertices in group i to those in group j; 
	and a vector to store a_i: the fraction of all ends of edges that are attached to vertices in group i*/
	graph e_ij_graph(N);
	std::vector<double> a_i_vector(N);
	double eij = (double)1 / E / 2; // initial e_ij; 
	for (int i = 0; i < N; i++) {
		boost::tie(ai, a_end) = boost::adjacent_vertices(i, initial_graph);
		for (; ai != a_end; ai++) {
			int j = *ai;
			if (i < j) {
				boost::add_edge(i, j, eij, e_ij_graph); //e_ij = e_ji; undirected
				//cout << "boost::add_edge(i, j, eij, e_ij_graph) " << i << "," << j
				//	<< " eij: " << eij << endl;
			}
		}
		double a_i = (double)in_degree(i, initial_graph) / E;
		a_i_vector[i] = a_i;

		//cout << "a_i_vector " << i << ": " << a_i << endl;
	}

	/*use a max heap to store deltaQ*/
	pairing_heap<node_FastNewman2004> heap;
	graph ij_heap_handleID(N);
	std::vector<handle_t_FastNewman2004> heap_handles;
	for (int i = 0; i < N; i++) {
		boost::tie(ai, a_end) = boost::adjacent_vertices(i, e_ij_graph);
		for (; ai != a_end; ai++) {
			int j = *ai;
			if (i < j) {
				double ec = get(boost::edge_weight_t(), e_ij_graph, boost::edge(i, j, e_ij_graph).first);
				double deltaQ = 2 * (ec - a_i_vector[i] * a_i_vector[j]);
				
				handle_t_FastNewman2004 y;
				heap_handles.insert(heap_handles.end(), y);
				int handleID = heap_handles.size() - 1;

				node_FastNewman2004 x;
				x.index = { i,j }; // i<j
				x.priority_value = deltaQ;
				heap_handles[handleID] = heap.push(x);

				

				boost::add_edge(i, j, handleID, ij_heap_handleID);

				//cout << "heap.push index: " << i << "," << j << " priority_value: " << deltaQ
				//	<< " handleID:" << handleID << endl;
				//cout << "boost::add_edge(i, j, handleID, ij_heap_handleID) " << i << "," << j
				//	<< " handleID: " << handleID << endl;
			}
		}
	}

	/*merge communties by pair using heaps*/
	while (heap.size() > 0) {

		node_FastNewman2004 top_element = heap.top();
		if (top_element.priority_value <= 0) {
			break; // the modularity cannot be increased anymore
		}
		heap.pop(); // top_element has been popped out, as the top pair of communities will be merged

		int c1 = top_element.index.first, c2 = top_element.index.second;


		//cout << endl << "top_element index: " << c1 << "," << c2 << " priority_value: " << top_element.priority_value
		//	<< endl;

		if (communities[c1].size() > 0 & communities[c2].size() > 0) { // neither c1 or c2 has been merged into other comm

			/*update a_c1*/
			double e_c1c2 = get(boost::edge_weight_t(), e_ij_graph, boost::edge(c1, c2, e_ij_graph).first);
			a_i_vector[c1] = a_i_vector[c1] + a_i_vector[c2] - e_c1c2;

			/*update e_kc1, kc1_heap_element*/
			std::vector<pair<int, int>> remove_edges;
			boost::tie(ai, a_end) = boost::adjacent_vertices(c1, e_ij_graph);
			for (; ai != a_end; ai++) {
				int k = *ai;
				pair<Edge, bool> ed = boost::edge(c2, k, e_ij_graph);
				if (ed.second) { // this edge does exist; k is connected to c2
					remove_edges.insert(remove_edges.end(), { k,c2 }); // we need to remove (k,c2) from e_ij_graph
					double e_kc1 = get(boost::edge_weight_t(), e_ij_graph, boost::edge(k, c1, e_ij_graph).first);
					double e_kc2 = get(boost::edge_weight_t(), e_ij_graph, boost::edge(k, c2, e_ij_graph).first);
					double new_e_kc1 = e_kc1 + e_kc2;
					pair<Edge, bool> ed2 = boost::edge(k, c1, e_ij_graph);
					boost::put(boost::edge_weight_t(), e_ij_graph, ed2.first, new_e_kc1); // update e_kc1

					int handleID = (int)get(boost::edge_weight_t(), ij_heap_handleID,
						boost::edge(k, c1, ij_heap_handleID).first);
					double deltaQ = 2 * (new_e_kc1 - a_i_vector[k] * a_i_vector[c1]);

					node_FastNewman2004 x;
					if (k < c1) {
						x.index = { k,c1 };
					}
					else {
						x.index = { c1,k };
					}
					x.priority_value = deltaQ;
					heap.update(heap_handles[handleID], x); // update kc1_heap_element

					//cout << "heap.update index: " << k << "," << c1 << " priority_value: " << deltaQ
					//	<< " handleID:" << handleID << endl;


				}
				/*else, k is not connected to c2, and e_kc1 and kc1_heap_element do not change*/
			}
			for (int i = 0; i < remove_edges.size(); i++) {
				int e1 = remove_edges[i].first;
				int e2 = remove_edges[i].second;
				boost::remove_edge(e1, e2, e_ij_graph); // communitiy k that connects both c1 and c2 is removed from c2_adj
	
				//cout << "boost::remove_edge(e1, e2, e_ij_graph) " << e1 << "," << e2 << endl;
			}


			/*no need to update a_c2*/

			/*check e_kc2, kc2_heap_element*/
			boost::tie(ai, a_end) = boost::adjacent_vertices(c2, e_ij_graph);
			for (; ai != a_end; ai++) {
				int k = *ai; // k is not connected to c1, otherwise this edge has been removed above
				if (k != c1) {
					/* we need to add e_kc1, kc1_heap_element*/
					double e_kc2 = get(boost::edge_weight_t(), e_ij_graph, boost::edge(k, c2, e_ij_graph).first);
					boost::add_edge(k, c1, e_kc2, e_ij_graph);
					//cout << "boost::add_edge(k, c1, e_kc2, e_ij_graph) " << k << "," << c1
					//	<< " e_kc2: " << e_kc2 << endl;
					double deltaQ = 2 * (e_kc2 - a_i_vector[k] * a_i_vector[c1]);
					handle_t_FastNewman2004 y;
					heap_handles.insert(heap_handles.end(), y);
					int handleID = heap_handles.size() - 1;

					node_FastNewman2004 x;
					if (k < c1) {
						x.index = { k,c1 };
					}
					else {
						x.index = { c1,k };
					}
					x.priority_value = deltaQ;
					heap_handles[handleID] = heap.push(x);

					boost::add_edge(k, c1, handleID, ij_heap_handleID);

					//cout << "heap.push index: " << k << "," << c1 << " priority_value: " << deltaQ
					//	<< " handleID:" << handleID << endl;
					//cout << "boost::add_edge(k, c1, handleID, ij_heap_handleID) " << k << "," << c1
					//	<< " handleID: " << handleID << endl;

				}
			}


			/*merge c2 into c1*/
			for (int i = 0; i < communities[c2].size(); i++) {
				vetex_2_communityID[communities[c2][i]] = c1;
			}
			communities[c1].insert(communities[c1].end(), communities[c2].begin(), communities[c2].end());
			communities[c2].clear();
			clear_vertex(c2, e_ij_graph);
			//remove_vertex(c2, e_ij_graph); // e_ij_graph only contains valid community_ID


		}


	}


	return vetex_2_communityID;


}
#pragma endregion FastNewman2004

#pragma region
std::vector<int> FastVincent2008(graph& initial_graph) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;

	int N = num_vertices(initial_graph), E = num_edges(initial_graph);

	double M = 0; // sum of edge costs
	for (int i = 0; i < N; i++) {
		boost::tie(ai, a_end) = boost::adjacent_vertices(i, initial_graph);
		for (; ai != a_end; ai++) {
			int j = *ai;
			if (i < j) {
				double ec = get(boost::edge_weight_t(), initial_graph, boost::edge(i, j, initial_graph).first);
				M = M + ec;
			}
		}
	}

	std::vector<pair<int, std::vector<int>>> communities(N); // pair<commu_ID,vertices>
	std::vector<int> vetex_2_communityID(N);
	/*every node is a community initially*/
	for (int i = 0; i < N; i++) {
		vetex_2_communityID[i] = i;
		communities[i].first = i;
		communities[i].second.insert(communities[i].second.end(), i);
	}

	/*record and update edge costs for communities*/
	std::vector<double> ec_in_communities(N, 0);
	std::vector<double> ec_incident_to_communities(N, 0);
	for (int i = 0; i < N; i++) {
		boost::tie(ai, a_end) = boost::adjacent_vertices(i, initial_graph);
		for (; ai != a_end; ai++) {
			int j = *ai;
			double ec = get(boost::edge_weight_t(), initial_graph, boost::edge(i, j, initial_graph).first);
			ec_incident_to_communities[i] = ec_incident_to_communities[i] + ec;
		}
	}
	graph ec_between_communities = copy_graph(initial_graph); // communities not in communities(N) will be cleared in it


	bool improved = true;
	while (improved == true) {

		//cout << "communities.size(): " << communities.size() << endl;

		///*print communities*/
		//cout << endl << "print communities" << endl;
		//for (int i = 0; i < communities.size(); i++) {
		//	cout << "communities " << i << ": <" << communities[i].first << ",{";
		//	for (int j = 0; j < communities[i].second.size(); j++) {
		//		cout << communities[i].second[j] << ",";
		//	}
		//	cout << "}" << endl;
		//}
		//cout << endl << endl;

		improved = false;

		int small_N = communities.size();
		std::vector<bool> isolated_node(small_N, true);
		
		for (int i = 0; i < small_N; i++) {

			if (isolated_node[i] == true) {

				double max_deltaQ = -1e10;
				int max_c2;

				int v1_in_smaller_network = i;
				int c1 = communities[v1_in_smaller_network].first;
				boost::tie(ai, a_end) = boost::adjacent_vertices(c1, ec_between_communities);
				for (; ai != a_end; ai++) {
					int c2 = *ai;
					double sum_in = ec_in_communities[c2];
					double sum_tot = ec_incident_to_communities[c2];
					double k_i = ec_incident_to_communities[c1];
					double k_i_in = get(boost::edge_weight_t(), ec_between_communities,
						boost::edge(c1, c2, ec_between_communities).first);
					double deltaQ = (sum_in + 2 * k_i_in) / 2 / M - pow((sum_tot + k_i) / 2 / M, 2)
						- sum_in / 2 / M + pow(sum_tot / 2 / M, 2) + pow(k_i / 2 / M, 2);
					if (max_deltaQ < deltaQ) {
						max_deltaQ = deltaQ;
						max_c2 = c2;
					}
				}

				/*merge c1 into max_c2*/
				if (max_deltaQ > 0) {

					improved = true;

					int v2_in_smaller_network;
					for (int j = 0; j < small_N; j++) {
						if (communities[j].first == max_c2) {
							v2_in_smaller_network = j;
							break;
						}
					}

					/*update isolated_node*/
					isolated_node[v1_in_smaller_network] = false;
					isolated_node[v2_in_smaller_network] = false;

					/*update ec_in_communities*/
					ec_in_communities[max_c2] = ec_in_communities[max_c2] + ec_in_communities[c1] +
						get(boost::edge_weight_t(), ec_between_communities,
							boost::edge(c1, max_c2, ec_between_communities).first);

					/*update ec_incident_to_communities*/
					ec_incident_to_communities[max_c2] = ec_incident_to_communities[max_c2] + 
						ec_incident_to_communities[c1]
						- get(boost::edge_weight_t(), ec_between_communities,
							boost::edge(c1, max_c2, ec_between_communities).first);

					/*update ec_between_communities and heap for c2*/
					boost::tie(ai, a_end) = boost::adjacent_vertices(c1, ec_between_communities);
					for (; ai != a_end; ai++) {
						int k = *ai;
						int k_in_smaller_network;
						for (int j = 0; j < small_N; j++) {
							if (communities[j].first == k) {
								k_in_smaller_network = j;
								break;
							}
						}
						if (k != max_c2) {
							pair<Edge, bool> ed = boost::edge(max_c2, k, ec_between_communities);
							if (ed.second) { // this edge does exist; k is connected to c2
								double e_kc1 = get(boost::edge_weight_t(), ec_between_communities,
									boost::edge(k, c1, ec_between_communities).first);
								double e_kc2 = get(boost::edge_weight_t(), ec_between_communities,
									boost::edge(k, max_c2, ec_between_communities).first);
								double new_e_kc2 = e_kc1 + e_kc2;
								pair<Edge, bool> ed2 = boost::edge(k, max_c2, ec_between_communities);
								boost::put(boost::edge_weight_t(), ec_between_communities, ed2.first, new_e_kc2); // update (k, c2)

								//cout << "new ec(" << k << "," << c2 << ")=" << new_e_kc2 << endl;

							}
							else { // this edge does not exist; push new (k_in_smaller_network,v2_in_smaller_network) in heap

								double e_kc1 = get(boost::edge_weight_t(), ec_between_communities,
									boost::edge(k, c1, ec_between_communities).first);
								boost::add_edge(k, max_c2, e_kc1, ec_between_communities);
							}
						}
					}


					/*merging isolated node c1 to c2*/
			        /*update vetex_2_communityID*/
					for (int i = 0; i < communities[v1_in_smaller_network].second.size(); i++) {
						vetex_2_communityID[communities[v1_in_smaller_network].second[i]] = max_c2;
					}
					/*update communities*/
					communities[v2_in_smaller_network].second.insert(communities[v2_in_smaller_network].second.end(),
						communities[v1_in_smaller_network].second.begin(), 
						communities[v1_in_smaller_network].second.end());
					communities[v1_in_smaller_network].second.clear();
					/*clear_vertex(c1, ec_between_communities)*/
					clear_vertex(c1, ec_between_communities);

				}

			}

			



		}


		/*erase empty communities*/
		for (int i = 0; i < communities.size(); i++) {
			if (communities[i].second.size() == 0) {
				communities.erase(communities.begin() + i);
				i--;
			}
		}
		

	}


	return vetex_2_communityID;

}
#pragma endregion FastVincent2008

#pragma region 
bool compare_int_pair(const pair<int, int>&i, const pair<int, int>&j)
{
	return i.second > j.second;  // < is from small to big; > is from big to small.  sort by the second item of pair<int, int>
}

void analyze_FastNewman2004_FastVincent2008(graph& DBLP_graph, graph& DBLP_group_graph, 
	std::vector<int>& vetex_2_communityID,
     int top_k, double alpha, int queried_skills_num, string save_name) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;


	/*metrics*/
	double avg_V = 0, avg_E_in = 0, avg_E_out = 0, avg_g_C = 0;

	int N = num_vertices(DBLP_graph), skill_N = num_vertices(DBLP_group_graph) - N;

	std::vector<std::vector<int>> communities(N);
	std::vector<pair<int, int>> community_sizes(N); // pair<commu_ID, size>
	for (int i = 0; i < N; i++) {
		community_sizes[i].first = i;
		/*vertex i is in communities[vetex_2_communityID[i]]*/
		communities[vetex_2_communityID[i]].insert(communities[vetex_2_communityID[i]].end(), i);
		community_sizes[vetex_2_communityID[i]].second++;
	}

	sort(community_sizes.begin(), community_sizes.end(), compare_int_pair); // from large size to small size


	for (int i = 0; i < top_k; i++) {
		//cout << "community_sizes[i].second: " << community_sizes[i].second << endl;
		avg_V = avg_V + (double)community_sizes[i].second / top_k;

		int commu_ID = community_sizes[i].first;
		std::vector<bool> skill_contained(skill_N, false);

		for (int j = 0; j < communities[commu_ID].size(); j++) {
			int v1 = communities[commu_ID][j];
			boost::tie(ai, a_end) = boost::adjacent_vertices(v1, DBLP_graph);
			for (; ai != a_end; ai++) {
				int v2 = *ai;
				if (vetex_2_communityID[v2] == commu_ID) { // this is an edge inside communities[commu_ID]
					if (v1 < v2) {
						avg_E_in = avg_E_in + (double)1 / top_k;
					}
				}
				else { // this is an edge connecting communities[commu_ID] to the outside
					avg_E_out = avg_E_out + (double)1 / top_k;
				}
			}
			boost::tie(ai, a_end) = boost::adjacent_vertices(v1, DBLP_group_graph);
			for (; ai != a_end; ai++) {
				int skill_ID = *ai - N;
				skill_contained[skill_ID] = true;
			}
		}

		/*randomly query skills*/
		std::vector<int> queried_skills;
		while (queried_skills.size() != queried_skills_num) {

			int skill_ID = N;
			while (skill_ID == N) {
				for (int k = 0; k < skill_N; k++) {
					if (skill_contained[k] == true & rand() < 0.2) {
						skill_ID = k;
						queried_skills.insert(queried_skills.end(), k);
						break;
					}
				}
			}			
			std::vector<int> experts; // experts with skill_ID
			boost::tie(ai, a_end) = boost::adjacent_vertices(N + skill_ID, DBLP_group_graph);
			for (; ai != a_end; ai++) {
				experts.insert(experts.end(), *ai);
			}
			for (int k = 0; k < experts.size(); k++) {
				int expert_ID = experts[k];
				boost::tie(ai, a_end) = boost::adjacent_vertices(expert_ID, DBLP_group_graph);
				for (; ai != a_end; ai++) {
					int skill = *ai - N; // a correlated skill
					bool added = false;
					for (int j = 0; j < queried_skills.size(); j++) {
						if (queried_skills[j] == skill) {
							added = true;
							break;
						}
					}
					if (added == false & skill_contained[skill] == true
						& queried_skills.size() < queried_skills_num) { // this correlated skill is new 
						queried_skills.insert(queried_skills.end(), skill); // add this skill to candidate_skills
					}
					if (queried_skills.size() == queried_skills_num) {
						break;
					}
				}
				if (queried_skills.size() == queried_skills_num) {
					break;
				}
			}

			if (queried_skills.size() < queried_skills_num) {
				cout << "candidate_skills.size() < selected_skills_num; reselect skills ..." << endl;
				queried_skills.clear();
			}

		}
		std::vector<bool> query_nodes(N, false);
		for (int k = 0; k < queried_skills_num; k++) {
			boost::tie(ai, a_end) = boost::adjacent_vertices(N + queried_skills[k], DBLP_group_graph);
			for (; ai != a_end; ai++) {
				query_nodes[*ai] = true;
			}
		}
		double g_C = 0;
		for (int j = 0; j < communities[commu_ID].size(); j++) {
			int v1 = communities[commu_ID][j];
			if (query_nodes[v1] == true) {
				g_C = g_C + alpha;
			}
			else {
				g_C = g_C - 1;
			}
		}

		avg_g_C = avg_g_C + (double)g_C / top_k;

	}


	ofstream outputFile;
	outputFile.precision(10);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open(save_name + ".csv");
	outputFile << "avg_V:," << avg_V << endl;
	outputFile << "avg_E:," << avg_E_in << endl;
	outputFile << "avg_E_in / avg_E_out:," << avg_E_in / avg_E_out << endl;
	outputFile << "avg_g_C:," << avg_g_C << endl << endl;
	outputFile.close();

}
#pragma endregion analyze_FastNewman2004_FastVincent2008

#pragma region
void step_by_step_code_analyses_FastNewman2004_FastVincent2008() {

	/*parameters*/
	int target_k = 1;
	bool connected_guarantee = false;
	int V = 1000000, E = 2000000;
	double ec_min = 1, ec_max = 10, nw_min = 1, nw_max = 10;
	int target_queryed_num = 3;
	int iteration_times = 1;

	for (int i = 0; i < iteration_times; i++) {

		vector<bool> query_nodes(V);
		graph input_graph;

		int new_graph = 1;
		if (new_graph == 1) {
			/*generate and save random graph*/
			input_graph = Generate_random_node_weighted_graph(connected_guarantee, V, E, ec_min, ec_max, nw_min, nw_max);
			query_nodes = Generate_random_query_nodes(V, target_queryed_num);
			save_node_weighted_graph("input_graph", input_graph, query_nodes);
			//print_vertices_and_edges(input_graph);
		}
		else {
			/*read graph*/
			input_graph = read_node_weighted_graph("input_graph.stp", query_nodes);
			cout << "print_vertices_and_edges(input_graph):" << endl;
			//print_vertices_and_edges(input_graph);
		}

		//std::vector<int> vetex_2_communityID = FastNewman2004(input_graph);

		std::vector<int> vetex_2_communityID = FastVincent2008(input_graph);


	}

}
#pragma endregion step_by_step_code_analyses_FastNewman2004_FastVincent2008

#pragma region 
void analyze_GBHA(graph& DBLP_graph, graph& DBLP_group_graph, 
	double alpha, double beta, int k, int queried_skills_num, int try_times, string save_name) {


	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;

	int N = num_vertices(DBLP_graph), skill_N = num_vertices(DBLP_group_graph) - N;

	/*metrics*/
	double avg_V = 0, avg_E_in = 0, avg_E_out = 0, avg_g_C = 0;


	for (int x = 0; x < try_times; x++) {

		std::vector<int> selected_skills;
		std::vector<bool> query_nodes;
		bool query_successful = false;
		while (1 > 0) {
			query_nodes = correlated_skills_for_application
			(DBLP_graph, DBLP_group_graph, queried_skills_num, selected_skills);
			if (query_nodes.size()  == N) {
				break;
			}
		}
		//int query_nodes_num = 0;
		//for (int i = 0; i < N; i++) {
		//	if (query_nodes[i] == true) {
		//		query_nodes_num++;
		//	}
		//}
		//cout << "query_nodes_num: " << query_nodes_num << endl;

		graph instance_graph = generate_PCSFP_instances(DBLP_graph, query_nodes, alpha, beta);

		vector<pair<vector<int>, vector<pair<int, int>>>> FGW_trees = FGW_clustering(instance_graph, k);
		vector<pair<vector<int>, vector<pair<int, int>>>> solutions_GBHA = GBHA(instance_graph, k, FGW_trees);

		for (int i = 0; i < k; i++) {

			int V = solutions_GBHA[i].first.size();
			avg_V = avg_V + (double)((double)V / k) / try_times;



			int E_in = 0;
			for (int j = 0; j < solutions_GBHA[i].first.size(); j++) {
				int v1 = solutions_GBHA[i].first[j];
				boost::tie(ai, a_end) = boost::adjacent_vertices(v1, DBLP_graph);
				for (; ai != a_end; ai++) {
					int v2 = *ai;
					if (v1 < v2) {
						bool v2_is_inside = false;
						for (int m = 0; m < solutions_GBHA[i].first.size(); m++) {
							if (v2 == solutions_GBHA[i].first[m]) {
								v2_is_inside = true;
								break;
							}
						}
						if (v2_is_inside == true) {
							E_in++;
						}
					}
				}
			}
			avg_E_in = avg_E_in + (double)((double)E_in / k) / try_times;

			int E_out = 0;
			for (int j = 0; j < solutions_GBHA[i].first.size(); j++) {
				int v1 = solutions_GBHA[i].first[j];
				boost::tie(ai, a_end) = boost::adjacent_vertices(v1, DBLP_graph);
				for (; ai != a_end; ai++) {
					int v2 = *ai;
					bool v2_is_outside = true;
					for (int m = 0; m < solutions_GBHA[i].first.size(); m++) {
						if (v2 == solutions_GBHA[i].first[m]) {
							v2_is_outside = false;
							break;
						}
					}
					if (v2_is_outside == true) {
						E_out++;
					}
				}
			}
			avg_E_out = avg_E_out + (double)((double)E_out / k) / try_times;

			double g_C = 0;
			for (int j = 0; j < solutions_GBHA[i].first.size(); j++) {
				int v1 = solutions_GBHA[i].first[j];
				if (query_nodes[v1] == true) {
					g_C = g_C + alpha;
				}
				else {
					g_C = g_C - 1;
				}
			}
			avg_g_C = avg_g_C + (double)((double)g_C / k) / try_times;

		}

	}

	ofstream outputFile;
	outputFile.precision(10);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open(save_name + ".csv");
	outputFile << "avg_V:," << avg_V << endl;
	outputFile << "avg_E:," << avg_E_in << endl;
	outputFile << "avg_E_in / avg_E_out:," << avg_E_in / avg_E_out << endl;
	outputFile << "avg_g_C:," << avg_g_C << endl << endl;
	outputFile.close();

}
#pragma endregion analyze_GBHA

#pragma region
void compare_case_study() {

	/*input DBLP graphs*/
	graph DBLP_graph, DBLP_group_graph;
	std::vector<string> DBLP_expert_names, DBLP_skill_names;
	read_DBLP_data(DBLP_graph, DBLP_group_graph, DBLP_expert_names, DBLP_skill_names);
	boost_graph_ec_update_pairwise_jaccard_distance(DBLP_graph);

	int N = num_vertices(DBLP_graph), skill_N = num_vertices(DBLP_group_graph) - N;
	double alpha = 1, beta = 1;
	


	
	/* analyze_GBHA*/
	int run_GBHA = 0;
	int top_k = 5, queried_skills_num = 10, try_times = 10;
	// larger top_k may include small communities that do not have enough correlated skills for Newman and Vincent
	if (run_GBHA == 1) {
		analyze_GBHA(DBLP_graph, DBLP_group_graph, alpha, beta, top_k, queried_skills_num, try_times
			, "compare_case_study_GBHA");
	}


	/* analyze_FastNewman2004*/
	int run_FastNewman2004 = 0;
	if (run_FastNewman2004 == 1) {
		std::vector<int> vetex_2_communityID = FastNewman2004(DBLP_graph);
		analyze_FastNewman2004_FastVincent2008(DBLP_graph, DBLP_group_graph, vetex_2_communityID, top_k, alpha,
			queried_skills_num, "compare_case_study_FastNewman2004");
	}
	
	/* analyze_FastVincent2008*/
	int run_FastVincent2008 = 1;
	if (run_FastVincent2008 == 1) {
		std::vector<int> vetex_2_communityID2 = FastVincent2008(DBLP_graph);
		analyze_FastNewman2004_FastVincent2008(DBLP_graph, DBLP_group_graph, vetex_2_communityID2, top_k, alpha,
			queried_skills_num, "compare_case_study_FastVincent2008");
	}


}
#pragma endregion compare_case_study







int main()
{
   srand(time(NULL)); //  seed random number generator
   
   auto begin = std::chrono::high_resolution_clock::now();

   experiments();

   auto end = std::chrono::high_resolution_clock::now();
   double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s


   cout << "END    runningtime: " << runningtime << "s" << endl;
   getchar();

}


