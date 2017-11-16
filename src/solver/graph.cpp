#include <queue>
#include <cassert>
#include <algorithm>
#include <iostream>
#include <fstream>

#include "graph.h"
// #include "slid_sat.h"
// #include "sl_sat.h"

// using namespace std;

/* --------------------------------------------------------------------------*/
/**
 * @synopsis  graph initialize a graph using abstraction
 *
 * @param f separation logic formula
 */
/* --------------------------------------------------------------------------*/

graph::graph(const graph& g)
{
	cc = g.cc;
	cycle = g.cycle;
	adj_list = g.adj_list;
}
graph& graph::operator=(const graph& g)
{
	if (this == &g)
		return *this;
	cc = g.cc;
	cycle = g.cycle;
	adj_list = g.adj_list;
}
graph::graph(graph&& g) noexcept
{
	cc = g.cc;
	cycle = g.cycle;
	adj_list = g.adj_list;
}
graph& graph::operator=(graph&& g) noexcept
{
	if (this == &g)
		return *this;
	cc = g.cc;
	cycle = g.cycle;
	adj_list = g.adj_list;
}
void graph::init(std::vector<std::set<int> >& eq_class_vec,  std::vector<std::pair<std::pair<int, int>, int> >& edge_vec)
{
	std::set<int> eq_class;
	/*create vertex*/
	for (size_t i = 0; i < eq_class_vec.size(); ++i) {
		eq_class = eq_class_vec[i];
		// add one vertex of index i
		boost::add_vertex(adj_list);
		// initialize the property of the ith vertex
		adj_list[i].insert(begin(eq_class), end(eq_class));
		// initialize the property of graph
		for (auto it = begin(eq_class); it != end(eq_class); ++it)
			adj_list[boost::graph_bundle][*it] = i;
	}


	/*create edge*/
	std::pair<std::pair<int, int>, int> edge;
	int src, dst;
	for (int i=0; i<edge_vec.size(); i++) {
		edge = edge_vec[i];
		src = adj_list[boost::graph_bundle][edge.first.first];
		dst = adj_list[boost::graph_bundle][edge.first.second];
		boost::add_edge(src, dst, edge.second, adj_list);
	}

	seek_cc();
	seek_cycle();
}

void graph::print_cc(std::vector<cc_t>& cc) {
	std::cout << "size of cc:" << cc.size() << std::endl;
	for (int i=0; i<cc.size(); i++) {
		cc_t c = cc[i];
		std::cout << "cc_" << i << ": [";
		std::set<int>::iterator it=c.begin();
		if (it != c.end()){
			std::cout << *it;
			++it;
		}

		for( ;it!=c.end(); ++it) {
			std::cout <<", " << *it;
		}
		std::cout << "]\n";
	}
	std::cout << std::endl;
}

void graph::print_cc() {
	print_cc(cc);
}



void graph::print_cyc() {
	std::cout << "size of cycles: " << cycle.size() << "\n";

	for (int i=0; i<cycle.size(); i++) {
		cc_cycle_t cc_cycle = cycle[i];
		std::cout << "cc_" << i << ": [\n";
		for (int j=0; j<cc_cycle.size(); j++) {
			cycle_t cyc = cc_cycle[j];
			std::cout << "cycle_" << j << ": [";
			for (int k=0; k<cyc.size(); k++) {
				std::cout << cyc[k] << ", ";
			}
			std::cout << "]\n";
		}
		std::cout<< "]\n" << std::endl;
	}

}

void graph::print() {
	std::cout << "print graph:\n";
	std::ofstream out("graph.dot");

	boost::property_map<adjacency_list, boost::vertex_index_t>::type index;
	typedef boost::graph_traits<adjacency_list>::vertex_iterator vertex_iter;
	std::pair<vertex_iter, vertex_iter> vp;
	adjacency_list::vertex_descriptor v;
	size_t num = boost::num_vertices(adj_list);
	std::cout << "num of vertices: " << num << std::endl;
	out << "digraph g {\n";
	for (vp=vertices(adj_list); vp.first!=vp.second; ++vp.first) {
		v = *vp.first;
		std::cout <<"size: " << adj_list[v].size() << " , index: " << index[v]  << std::endl;
		std::set<int> node = adj_list[v];
		out << "node_" << index[v] << " [label=\"[";
		std::set<int>::iterator it=node.begin();
		if (it != node.end()){
			out << *it;
			++it;
		}

		for( ;it!=node.end(); ++it) {
			out <<", " << *it;
		}
		out <<"]\"];\n\n";
	}
	std::cout << std::endl;



	adjacency_list::vertex_descriptor  v1, v2;
	typedef boost::graph_traits<adjacency_list>::edge_iterator edge_iter;
	std::pair<edge_iter, edge_iter> ep;
	edge_iter ei, ei_end;
	for (tie(ei, ei_end)=edges(adj_list); ei!=ei_end; ++ei) {
		v1 = boost::source(*ei, adj_list);
		v2 = boost::target(*ei, adj_list);
		std::cout << "(" << *adj_list[v1].begin() << ") ---";
		std::cout << adj_list[*ei] ;
		std::cout << "--- (" << *adj_list[v2].begin() << ")";
		std::cout<< std::endl;

		out << "node_" << index[v1] << "->" << "node_" << index[v2] << "[label=\"";
		out << adj_list[*ei];
		out<<"\"];\n";
	}
	std::cout << std::endl;
	out << "}\n";
	out.close();
}

/* --------------------------------------------------------------------------*/
/**
 * @synopsis  get_edge_property
 *
 * @param u   vertex index u
 * @param v
 *
 * @return    edge property representing spatial atom id
 *		  -1 no edge between u and v
 */
/* --------------------------------------------------------------------------*/
int graph::get_edge_property(size_t u, size_t v) const
{
	adjacency_list::out_edge_iterator it1, it2;
	tie(it1, it2) = boost::out_edges(u, adj_list);
	for (; it1 != it2; ++it1) {
		if (v == boost::target(*it1, adj_list))
			return adj_list[*it1];
	}
	return -1;
}
int graph::get_edge_property(edge_descriptor e)
{
	return get_edge_property(source(e), target(e));
}
/* --------------------------------------------------------------------------*/
/**
 * @synopsis  seek_cc calculate the connected components
 */
/* --------------------------------------------------------------------------*/
void graph::seek_cc()
{
	if (cc.size() > 0) cc.clear();
	size_t i, j, k;
	adjacency_list::out_edge_iterator out_it1, out_it2;
	adjacency_list::in_edge_iterator in_it1, in_it2;
	std::deque<int> q;
	std::set<int> t;
	size_t num = boost::num_vertices(adj_list);
	std::vector<int> visited(num);

	for (i = 0; i < visited.size(); ++i)
		visited[i] = 0;

	for (i = 0; i < num; ++i) {
		if (visited[i])
			continue;
		q.push_back(i);
		t.clear();
		while (!q.empty()) {
			j = q.front();
			visited[j] = 1;
			t.insert(j);
			tie(in_it1, in_it2) = boost::in_edges(j, adj_list);
			for (; in_it1 != in_it2; ++in_it1) {
				k = boost::source(*in_it1, adj_list);
				if (!(visited[k]) && (find(begin(q), end(q), k) == end(q)))
					q.push_back(k);
			}
			tie(out_it1, out_it2) = boost::out_edges(j, adj_list);
			for (; out_it1 != out_it2; ++out_it1) {
				k = boost::target(*out_it1, adj_list);
				if (!(visited[k]) && (find(begin(q), end(q), k) == end(q)))
					q.push_back(k);
			}
			q.pop_front();
		}
		cc.push_back(t);
	}
}
/* --------------------------------------------------------------------------*/
/**
 * @synopsis  seek_cycle calculate the cycle of the graph
 */
/* --------------------------------------------------------------------------*/
void graph::seek_cycle()
{
	if (cycle.size()>0) cycle.clear();
	size_t i, j;
	std::vector<std::vector<int>> t;
	adjacency_list::out_edge_iterator it1, it2;
	std::vector<int> c, t1, s;
	std::map<int, bool> m;
	for (i = 0; i < cc.size(); ++i) {
		c.assign(begin(cc[i]), end(cc[i]));

		// cc [1,2,3,...]
		for (j = 0; j < c.size(); ++j)
			m[c[j]] = false;
		t.clear();
		for (j = 0; j < c.size(); ++j) {
			if (m[c[j]])
				continue;
			s.push_back(c[j]); // s [1->x->y->...]
			while (!s.empty()) {
				t1.clear();
				size_t k = s.back();
				if (!m[k]) {
					tie(it1, it2) = boost::out_edges(k, adj_list);
					for (; it1 != it2; ++it1) {
						size_t tar = boost::target(*it1, adj_list);
						auto it = find(begin(s), end(s), tar);
						if (it != end(s)) {
							t1.insert(end(t1), it, end(s)); // it->...->end(s)->it
							t.push_back(t1);
						}
					}
					m[k] = true;
				}
				tie(it1, it2) = boost::out_edges(k, adj_list);
				for (; it1 != it2; ++it1) {
					size_t tar = boost::target(*it1, adj_list);
					if(!m[tar]) {
						s.push_back(tar);
						break;
					}
				}
				if (it1 == it2)
					s.pop_back();

			}
		}
		cycle.push_back(t);
	}
}

/* --------------------------------------------------------------------------*/
/**
 * @synopsis  is_dag_like
 * @return
 */
/* --------------------------------------------------------------------------*/
bool graph::is_dag_like() const
{
	assert(!cycle.empty());
	size_t i, j, k;
	adjacency_list::out_edge_iterator it1, it2;
	std::set<int> v_out_cycle;//

	for (i = 0; i < cycle.size(); ++i) {
		if (cycle[i].size() > 1)
			return false;

		if (cycle[i].size() == 0) continue;
		v_out_cycle.clear();
		v_out_cycle.insert(begin(cc[i]), end(cc[i]));

		for (k = 0; k < cycle[i][0].size(); ++k) {
			v_out_cycle.erase(cycle[i][0][k]);
		}
		// v_out_cycle -> cycle reachability
		for (auto v : v_out_cycle) {
			bool flag = false;
			for (auto u : cycle[i][0]) {
				std::vector<graph::edge_descriptor> res = get_path(v, u);
				if (!res.empty()) {flag=true;break;}
			}
			if (!flag) return false;
		}
	}
	return true;
}

std::vector<int> graph::get_cc_cycle_num() const
{
	std::vector<int> res(cc.size());

	for (size_t i = 0; i < cycle.size(); ++i)
		res[i] = cycle[i].size();

	return res;
}

std::vector<graph::cc_cycle_t>& graph::get_cc_cycle()
{
	return cycle;
}

int graph::which_cc(size_t v) const
{
	for (size_t i = 0; i < cc.size(); ++i) {
		auto it = std::find(begin(cc[i]), end(cc[i]), v);
		if (it != end(cc[i]))
			return i;
	}
	return -1;
}

std::pair<int, int> graph::get_cycle_coord(size_t v) const
{
	int i = which_cc(v);
	int j;
	for (size_t k = 0; k < cycle[i].size(); ++k) {
		auto it = std::find(begin(cycle[i][k]), end(cycle[i][k]), v);
		if (it != end(cycle[i][k]))
			return std::make_pair(i, k);
	}
	return std::make_pair(-1, -1);
}

std::pair<int, int> graph::get_cycle_coord(edge_descriptor e) const
{
	return get_cycle_coord(boost::source(e, adj_list));
}

bool graph::is_cycle(const std::pair<int, int>& coord) const
{
	return (coord.first >= 0 && coord.second >= 0);
}

std::vector<int> graph::get_cycle(const std::pair<int, int>& coord) const
{
	return cycle[coord.first][coord.second];
}

std::vector<graph::edge_descriptor> graph::merge_path(std::vector<graph::edge_descriptor>& path1, std::vector<graph::edge_descriptor>& path2)
{
	std::vector<edge_descriptor> res(path1);
	res.insert(end(res), begin(path2), end(path2));
	return res;
}

std::vector<graph::edge_descriptor> graph::merge_path(std::vector<graph::edge_descriptor>& path1, std::vector<int>& c) const
{
	std::vector<edge_descriptor> res(path1);
	edge_descriptor e = path1[path1.size()-1];
	out_edge_iterator ei, ei_end;
	std::vector<int>::iterator it, it2;
	size_t v = boost::target(e, adj_list);
	it = std::find(begin(c), end(c), v);
	for (it2 = it; it2 != end(c); ++it2) {
		tie(ei, ei_end) = boost::out_edges(*it2, adj_list);
		res.push_back(*ei);
	}
	for (it2 = begin(c); it2 != it; ++it2) {
		tie(ei, ei_end) = boost::out_edges(*it2, adj_list);
		res.push_back(*ei);
	}
	return res;
}

std::vector<std::pair<int, int>> graph::get_cycle_coords() const
{
	std::vector<std::pair<int, int>> res;
	for (size_t i = 0; i < cycle.size(); ++i) {
		for (size_t j = 0; j < cycle[i].size(); ++j)
			res.push_back(std::make_pair(i, j));
	}
	return res;
}
std::vector<graph::edge_descriptor> graph::get_path(size_t u)
{
	std::vector<edge_descriptor> res;
	std::pair<int, int> coord = get_cycle_coord(u);
	if (!is_cycle(coord))
		return res;

	std::vector<int> c = get_cycle(coord);
	out_edge_iterator ei, ei_end;
	std::vector<int>::iterator it, it2;
	it = std::find(begin(c), end(c), u);
	for (it2 = it; it2 != end(c); ++it2) {
		tie(ei, ei_end) = boost::out_edges(*it2, adj_list);
		res.push_back(*ei);
	}
	for (it2 = begin(c); it2 != it; ++it2) {
		tie(ei, ei_end) = boost::out_edges(*it2, adj_list);
		res.push_back(*ei);
	}
	return res;
}

std::vector<graph::edge_descriptor> graph::get_path(size_t u, size_t v) const
{
	assert(u != v);
	std::vector<edge_descriptor> r;

	int i = which_cc(u);
	if (i != which_cc(v))
		return r;

	std::vector<int> t;
	std::vector<edge_descriptor> s;
	t.assign(begin(cc[i]), end(cc[i]));
	std::vector<int> visited(t.size());
	std::map<int, int> m;
	for (size_t i = 0; i < t.size(); ++i)
		m[t[i]] = i;
	return get_path(u, v, s, visited, m);
}

std::vector<graph::edge_descriptor> graph::get_path(size_t u, size_t v,
													std::vector<edge_descriptor>& s, std::vector<int>& visited,
													std::map<int, int>& m) const
{
	if (u == v) return s;
	std::vector<edge_descriptor> res;
	visited[m[u]] = 1;
	out_edge_iterator ei, ei_end;
	tie(ei, ei_end) = boost::out_edges(u, adj_list);
	for (; ei != ei_end; ++ei) {
		size_t targ = boost::target(*ei, adj_list);
		if (!visited[m[targ]]) {
			s.push_back(*ei);
			res = get_path(targ, v, s, visited, m);
			if (!res.empty())
				break;
			s.pop_back();
		}
	}
	return res;
}

std::pair<graph::edge_iterator, graph::edge_iterator> graph::get_edge()
{
	return boost::edges(adj_list);
}

size_t graph::var_to_ver(size_t vid)
{
	return adj_list[boost::graph_bundle][vid];
}
size_t graph::source(edge_descriptor e)
{
	return boost::source(e, adj_list);
}
size_t graph::target(edge_descriptor e)
{
	return boost::target(e, adj_list);
}
