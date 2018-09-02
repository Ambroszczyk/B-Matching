#include <iostream>
#include <vector>
#include <algorithm>
#include <fstream>
#include <map>
#include <regex>
#include <atomic>
#include <queue>
#include <thread>
#include <mutex>
#include <memory>
#include "blimit.hpp"
#include <limits>
#include <set>
#include <future>

using NodeT = unsigned long;
using Adj_listT = std::vector<std::pair<NodeT, int>>;
using GraphT = std::vector<Adj_listT>;
GraphT graph;

std::vector<NodeT> old_indices;

struct comp {
    bool operator() (const std::pair<int, NodeT>& a,
    const std::pair<int, NodeT>& b) {
        return a.first == b.first ? old_indices[a.second] >
                old_indices[b.second] : a.first > b.first;
    }
};
using Prior_queT =
std::priority_queue<std::pair<int, NodeT>, std::vector<std::pair<int, NodeT>>,
        comp>;
using Priors_listT = std::vector<Prior_queT>;

Priors_listT suitors;

using SpinlocksT = std::unique_ptr<std::atomic<bool>[]>;
SpinlocksT s_vertex;
std::atomic<bool> s_v_queue;
std::atomic<bool> s_next_v_queue;

//For given vertex v, t_next[v] points next eligible friend of v.
std::vector<NodeT> t_next;

std::queue<NodeT> v_queue;
std::queue<NodeT> next_v_queue;

std::vector<NodeT> b;
using AtomicsT = std::unique_ptr<std::atomic<NodeT>[]>;
AtomicsT bd;
std::vector<NodeT> primary_b;

struct my_pair {
    int first;
    int second;
};

std::vector<std::atomic<my_pair>> last;


const NodeT EMPTY_QUEUE_IDX = std::numeric_limits<NodeT>::max();

void P(std::atomic<bool>& mut) {
    bool t = true;
    while (!mut.compare_exchange_weak(t, false))
        t = true;
}

void V(std::atomic<bool>& mut) {
    mut.store(true);
}

inline NodeT give_graph_idx(NodeT, std::map<NodeT, NodeT>&);

void file_to_graph(std::string &filename) {
    std::string line;
    std::ifstream file(filename);
    std::map<NodeT, NodeT> v_map;


    while (getline(file, line)) {
        if (line[0] != '#') { //line is not a comment
            NodeT v1, v2, v1_idx, v2_idx;
            int e;
            std::stringstream ss(line);
            ss >> v1 >> v2 >> e;

            v1_idx = give_graph_idx(v1, v_map);
            v2_idx = give_graph_idx(v2, v_map);

            graph[v1_idx].emplace_back(std::make_pair(v2_idx, e));
            graph[v2_idx].emplace_back(std::make_pair(v1_idx, e));
        }
    }
}

inline NodeT give_graph_idx(NodeT v, std::map<NodeT, NodeT>& v_map) {
    if (v_map.count(v)) {
        return v_map[v];
    }
    else {
        NodeT size = graph.size();
        graph.emplace_back(Adj_listT());
        old_indices.push_back(v);
        v_map[v] = size;
        return size;
    }
}

inline void sort_vertex_edges(NodeT idx) {
    std::sort(graph[idx].begin(), graph[idx].end(),
              [](const std::pair<NodeT, int>& a,
                 const std::pair<NodeT, int>& b) -> bool {
                  return a.second == b.second ? old_indices[a.first] >
                          old_indices[b.first] : a.second > b.second;
              });
}

void thread_sort_vertex_edges(std::atomic<NodeT>& next) {
    NodeT act_idx = next++;
    while (act_idx < graph.size()) {
        sort_vertex_edges(act_idx);
        act_idx = next++;
    }
    return;
}

//multi-thread function
void sort_all_vertices_edges(int threads_num) {
    std::atomic<NodeT> next(0);
    std::vector<std::thread> threads_vect;

    for (int i = 0; i < threads_num; i++) {
        std::thread t{[&next]{
            thread_sort_vertex_edges(next);
        }};
        threads_vect.push_back(std::move(t));
    }
    thread_sort_vertex_edges(next);
    for (int i = 0; i < threads_num; i++) {
        threads_vect.back().join();
        threads_vect.pop_back();
    }
}

//assume all vertices are numbered like 0,1,2..
inline void init_prior_queues() {
    for (NodeT i = 0; i < graph.size(); i++) {
        suitors.emplace_back(Prior_queT());
    }
}

inline void init_spinlocks() {
    s_vertex = std::make_unique<std::atomic<bool>[]>(graph.size());
    for (int i = 0; i < graph.size(); i++) {
        s_vertex[i].store(true);
    }
}

inline void init_t_next() {
    for (size_t i = 0; i < graph.size(); i++) {
        t_next.emplace_back(0);
    }
}

inline void init_last() {
    std::vector<std::atomic<my_pair>> v(graph.size());
    std::swap(v, last);
    for (NodeT i = 0; i < graph.size(); i++) {
        last[i].store({-1, -1});
    }
}

inline void init_bd() {
    bd = std::make_unique<std::atomic<NodeT>[]>(graph.size());
}

inline void fill_queue() {
    for (NodeT i = 0; i < graph.size(); i++) {
        v_queue.push(i);
    }
}

inline void set_b(unsigned int b_method_num) {
    for (NodeT i = 0; i < graph.size(); i++) {
        b[i] = bvalue(b_method_num, old_indices[i]);
    }
}

//e - potential partner for v
bool is_eligible(NodeT e_idx, NodeT v_idx, int e_v_edge) {
    if (primary_b[e_idx] == 0)
        return false;
    my_pair top = last[e_idx].load();
    bool are_suitors_full = (top.second != -1);
    if (are_suitors_full) {
        NodeT top_idx = static_cast<NodeT>(top.second);
        int top_edge = top.first;
        if (top_edge < e_v_edge
            || (top_edge == e_v_edge
                && old_indices[top_idx] < old_indices[v_idx]))
            return true;
        return false;
    }
    else
        return true;
}

//under lock on e
void make_suitor(NodeT e_idx, NodeT v_idx, int e_v_edge) {
    //if prior_queue is full
    if (suitors[e_idx].size() == primary_b[e_idx]) {
        NodeT top_idx = suitors[e_idx].top().second;
        suitors[e_idx].pop();

        //atomic operation
        if (++bd[top_idx] == 1) {
                P(s_next_v_queue);
                next_v_queue.push(top_idx);
                V(s_next_v_queue);
        }
    }
    suitors[e_idx].push(std::pair<int, NodeT>(e_v_edge, v_idx));
    if (suitors[e_idx].size() == primary_b[e_idx]) {
        last[e_idx].store({suitors[e_idx].top().first,
                           static_cast<int>(suitors[e_idx].top().second)});
    }
}

//take first element from queue or end execution
NodeT next_vertex_from_v_queue() {
        NodeT v_idx;

        if (v_queue.empty())
            return EMPTY_QUEUE_IDX;

        P(s_v_queue);
        if (v_queue.empty())
            v_idx = EMPTY_QUEUE_IDX;
        else {
            v_idx = v_queue.front();
            v_queue.pop();
        }
        V(s_v_queue);
        return v_idx;
    }

void thread_find_b_matching() {
    NodeT v_idx = next_vertex_from_v_queue();
    while (v_idx != EMPTY_QUEUE_IDX) {
        unsigned int i = 0;
        //two threads can not have the same v_idx!
        NodeT adj_list_size = graph[v_idx].size();
        while (i < b[v_idx] && t_next[v_idx] != adj_list_size) {
            //threads can not modify t_next simultaneously
            //eligible partner
            NodeT e_idx = graph[v_idx][t_next[v_idx]].first;
            int e_v_edge = graph[v_idx][t_next[v_idx]].second;
            if (is_eligible(e_idx, v_idx, e_v_edge)) {
                P(s_vertex[e_idx]);
                    if (is_eligible(e_idx, v_idx, e_v_edge)) {
                    i++;
                    //if prior was full adds vertex to next_v_queue
                    make_suitor(e_idx, v_idx, e_v_edge);
                }
                V(s_vertex[e_idx]);
            }
            t_next[v_idx]++;
        }
        v_idx = next_vertex_from_v_queue();
    }
}

void update_b_using_bd() {
    for (size_t i = 0; i < b.size(); i++) {
        b[i] = bd[i];
        bd[i] = 0;
    }
}


void find_b_matching(unsigned int b_method_num, int threads_num) {
    fill_queue();
    set_b(b_method_num);
    primary_b = b;

    while (!v_queue.empty()) {
        std::vector<std::thread> threads_vect;
        for (int i = 0; i < threads_num; i++) {
            std::thread t{[]{
                thread_find_b_matching();
            }};
            threads_vect.push_back(std::move(t));
        }
        thread_find_b_matching();
        for (int i = 0; i < threads_num; i++) {
            threads_vect.back().join();
            threads_vect.pop_back();
        }

        //v_queue is empty
        std::swap(v_queue, next_v_queue);
        update_b_using_bd();
    }
}


void clean_and_print_result(int thread_num) {
    int res = 0;
    NodeT act_idx = 0;

    while (act_idx < graph.size()) {
        while (!suitors[act_idx].empty()) {
            res += suitors[act_idx].top().first;
            suitors[act_idx].pop();
        }
        last[act_idx].store({-1, -1});
        act_idx++;
    }

    std::fill(t_next.begin(), t_next.end(), 0);
    std::cout << res / 2 << "\n";
}

int main(int argc, char *argv[]) {
    int thread_count = std::stoi(argv[1]);
    int available_threads_number = thread_count - 1;
    int b_limit = std::stoi(argv[3]);
    std::string input_filename{argv[2]};

    file_to_graph(input_filename);

    sort_all_vertices_edges(available_threads_number);


    init_prior_queues();
    init_last();
    init_spinlocks();
    init_t_next();
    b.resize(graph.size());
    init_bd();
    s_v_queue.store(true);
    s_next_v_queue.store(true);

    for (int i = 0; i <= b_limit; i++) {
        find_b_matching(i, available_threads_number);
        clean_and_print_result(available_threads_number);
    }
}
