#include<iostream>
#include<fstream>
#include<map>
#include<vector>
#include<set>
#include<utility>
#include<algorithm>
#include<iomanip> 
using namespace std;

typedef struct {
	int a,b;
} Edge;

bool operator<(Edge e1, Edge e2) {
	return e1.a<e2.a || (e1.a==e2.a && e1.b<e2.b);
}

class TemporalGraph {
    public:
    int timestamps;
    int vertices;
    int edges;
	string name;

    vector<Edge> get_edges(int timestamp) {
        return time2edges[timestamp];
    }

    TemporalGraph(string dataset_path) {
        ifstream in(dataset_path);

		name = get_dataset_name(dataset_path);

        in >> timestamps >> vertices >> edges;

        print_info(dataset_path);

        int _t, _a, _b;

        for(int i = 0; i < edges; i++) {   
            in >> _t >> _a >> _b;
            time2edges[_t].push_back(Edge{_a, _b});
        }

        in.close();
    }

    private:
    map<int, vector<Edge>> time2edges;

    string get_dataset_name(string dataset_path) {
        string name = "";
        bool add = false;

        for(int i = 0; i < dataset_path.length(); i++) {
            if(dataset_path[i] == '.') add = false;
            if(add) name += dataset_path[i];
            if(dataset_path[i] == '/') add = true;
        }

        return name;
    }

    void print_info(string dataset_path) {
        cout << "-----------dataset-----------" << endl;
        cout << "Name: " << name << endl;
        cout << "-----------info--------------" << endl;
        cout << "Number of timestamps: " << timestamps << endl;
        cout << "Number of vertices: " << vertices << endl;
        cout << "Number of edges: " << edges << endl;
        cout << "-----------------------------" << endl;
    }
};

vector<Edge> get_intersection(const vector<Edge> &a, const vector<Edge> &b) {
    vector<Edge> res;
    set_intersection(a.begin(), a.end(), b.begin(), b.end(), std::inserter(res, res.begin()));
    return res;
}

vector<Edge> get_difference(const vector<Edge> &a, const vector<Edge> &b) {
    vector<Edge> res;
    set_difference(a.begin(), a.end(), b.begin(), b.end(), std::inserter(res, res.begin()));
    return res;
}

vector<Edge> get_union(const vector<Edge> &a, const vector<Edge> &b) {
    vector<Edge> res;
    set_union(a.begin(), a.end(), b.begin(), b.end(), std::inserter(res, res.begin()));
    return res;
}

// GLOBAL
int n, m;
time_t t_start, t_end;

typedef map<int,int> MII;
typedef vector<int> VI;
typedef MII::iterator EdgeIter;

const int maxClass=1000;

VI mapto;
VI deg, bin;
vector<Edge> binEdge;
vector<VI> A;
vector<MII> adj, pos;

int cntClass[maxClass];
int k_max = 0;

inline bool compVertex(int i, int j) {
	return deg[i]<deg[j] || (deg[i]==deg[j] && i<j);
}

inline void orderPair(int &u, int &v) {
	if (!compVertex(u,v)) swap(u,v);
}

inline void printClass(int u, int v, int cls) {
	++cntClass[cls];
    k_max = max(k_max, cls);
	//cout << "(" << u << "," << v << "):" << cls << endl;
}

inline void updateSupport(int u, int v, int delta) {
	adj[u][v]+=delta;
	adj[v][u]+=delta;
}

inline void removeEdge(int u, int v) {
	adj[u].erase(v);
	adj[v].erase(u);
}

void reorder() {
	mapto.resize(n);
	for (int i=0; i<n; ++i) mapto[i]=i;
	sort(mapto.begin(), mapto.end(), compVertex);
}

void intersect(const VI &a, const VI &b, VI &c) {
	c.clear();
	unsigned j=0;
	for (unsigned i=0; i<a.size(); ++i) {
		while (j<b.size() && b[j]>a[i]) ++j;
		if (j>=b.size()) break;
		if (b[j]==a[i]) c.push_back(a[i]);
	}
}

void countTriangles() {
	A.resize(n);
	for (int i=0; i<n; ++i) A[i].clear();
	int nDeltas=0;
	for (int vi=n-1; vi>=0; --vi) {
		int v=mapto[vi];
		for (EdgeIter it = adj[v].begin(); it!=adj[v].end(); ++it) {
			int u = it->first;
			if (!compVertex(u,v)) continue;
			VI common;
			intersect(A[u], A[v], common);
			for (unsigned i=0; i<common.size(); ++i) {
				int w=mapto[common[i]];
				++nDeltas;
				updateSupport(u,v,1);
				updateSupport(v,w,1);
				updateSupport(w,u,1);
			}
			A[u].push_back(vi);
		}
	}
	//cout << nDeltas << " triangles found.\n";
}

void binSort() {
	bin.clear(); bin.resize(n,0);
	int nBins=0;
	int mp=0;
	for (int u=0; u<n; ++u) {
		MII tadj = adj[u];
		for (EdgeIter it=tadj.begin(); it!=tadj.end(); ++it) {
			int v=it->first;
			if (!compVertex(u,v)) continue;
			int sup=it->second;
			if (sup==0) {
				printClass(u,v,2);
				removeEdge(u,v);
				continue;
			}
			++mp;
			++bin[sup];
			nBins=max(sup,nBins);
		}
	}
	m=mp;
	++nBins;
	int count=0;
	for (int i=0; i<nBins; ++i) {
		int binsize=bin[i];
		bin[i]=count;
		count+=binsize;
	}
	pos.clear(); pos.resize(n);
	for (int i=0; i<n; ++i) pos[i].clear();
	binEdge.resize(m);
	for (int u=0; u<n; ++u)
		for (EdgeIter it=adj[u].begin(); it!=adj[u].end(); ++it) {
			int v=it->first;
			if (!compVertex(u,v)) continue;
			int sup=it->second;
			Edge e={u,v};
			int &b=bin[sup];
			binEdge[b]=e;
			pos[u][v]=b++;
		}
	for (int i=nBins; i>0; --i) bin[i]=bin[i-1];
	bin[0]=0;
}

void updateEdge(int u, int v, int minsup) {
	orderPair(u,v);
	int sup=adj[u][v];
	if (sup<=minsup) return;
	int p=pos[u][v];
	int posbin=bin[sup];
	Edge se=binEdge[posbin];
	Edge e{u,v};
	if (p!=posbin) {
		pos[u][v]=posbin;
		pos[se.a][se.b]=p;
		binEdge[p]=se;
		binEdge[posbin]=e;
	}
	++bin[sup];
	updateSupport(u,v,-1);
}

void trussDecomp() {
	for (int s=0; s<m; ++s) {
		int u=binEdge[s].a;
		int v=binEdge[s].b;
		orderPair(u,v);
		int supuv=adj[u][v];
		printClass(u,v,supuv+2);
		int nfound=0;
		for (EdgeIter it=adj[u].begin(); it!=adj[u].end(); ++it) {
			if (nfound==supuv) break;
			int w=it->first;
			if (w==v) continue;
			if (adj[v].find(w)!=adj[v].end()) {
				++nfound;
				updateEdge(u,w,supuv);
				updateEdge(v,w,supuv);
			}
		}
		removeEdge(u,v);
	}
}

void print_exec_time() {
	cout << "-----------------------------" << endl; 
	double time_taken = double(t_end - t_start) / double(CLOCKS_PER_SEC); 
    cout << "Execution time: " << fixed << time_taken << setprecision(5); 
    cout << " sec " << endl;
	cout << "-----------------------------" << endl; 
}

void print_info(int t_s, int N) {
	int MOD_INFO = 5;
	if(t_s % MOD_INFO == 0) cerr << t_s << " of " << N << endl; 
}

void maximal_spantrusses(string dataset_path) {
    TemporalGraph tgraph = TemporalGraph(dataset_path);
	t_start = clock();

    n = tgraph.vertices;
    m = tgraph.edges;
    vector<int> K(tgraph.timestamps + 1, 0);
    vector<int> TM;

    for(int t_s = 0; t_s < tgraph.timestamps; t_s++) {
		print_info(t_s, tgraph.timestamps);

        vector<vector<Edge>> differences;
        vector<Edge> intersection = tgraph.get_edges(t_s);

        int t_e = t_s + 1;
        for(; t_e < tgraph.timestamps; t_e++) {
            vector<Edge> tmp = get_intersection(intersection, tgraph.get_edges(t_e));
            if(tmp.empty()) break;
            differences.push_back(get_difference(intersection, tmp));
            intersection = tmp;
        }
        differences.push_back(intersection);
        
        t_e--;
        vector<Edge> temporal_edges;

        int k_ii = 0;
        
        for(; t_e >= t_s; t_e--) {
            temporal_edges = get_union(temporal_edges, differences[t_e - t_s]);

            int lb = max(K[t_e], k_ii);

            deg.resize(tgraph.vertices);
            fill(deg.begin(), deg.end(), 0);
            adj.clear();
            adj.resize(n);
			
            for(int i = 0; i < n; i++) adj[i].clear();
            
            for(auto e : temporal_edges) {
                deg[e.a]++;
                deg[e.b]++;
                adj[e.a][e.b] = 0;
                adj[e.b][e.a] = 0;
            }

            // from "Truss Decomposition in Massive Networks"
            reorder();
	        countTriangles();
	        binSort();
	        trussDecomp();

            if(k_max > lb) TM.push_back(k_max);
            //k_ii = max(k_max, k_ii);
			k_ii = k_max;
            K[t_e] = max(K[t_e], k_ii);
            k_max = 0;
        }
    }

	t_end = clock();
	
    cout << TM.size() << endl;
	cout << "-----------------------------" << endl; 
	double time_taken = double(t_end - t_start) / double(CLOCKS_PER_SEC); 
    cout << "Execution time: " << fixed << time_taken << setprecision(5); 
    cout << " sec " << endl;
	cout << "-----------------------------" << endl;

	//print_exec_time();
}

int main(int args, char* argv[]) {
    if(args != 2) {
        cout << "! Error !" << endl;
        cout << "Usage: ./main dataset_path" << endl;
        cout << "-----------------------" << endl;
        system("ls -1 datasets");
        cout << "-----------------------" << endl;
        exit(0);
    }
    string dataset_path = argv[1];
    maximal_spantrusses(dataset_path);
    return 0;
}