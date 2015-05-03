#include <iostream>
#include <fstream>
#include <vector>
#include <cstring>
#include <string>
#include <cassert>
#include <algorithm>
#include <queue>
#include <map>

using namespace std;

typedef int VertexId;
typedef int NodeId;

const int ALPSIZE = 52 + 15 + 10;
const int SPECSIZE = 10;
const char ALP[ALPSIZE] = {
'a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z',
'A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P','Q','R','S','T','U','V','W','X','Y','Z',
'0','1','2','3','4','5','6','7','8','9',
'!','[',']','(',')',',','.','\'','/','\"',';','-','+','*','_'};

const char SPEC[SPECSIZE] = {
'.','^','(',')','[',']','*','+','?','|'};


struct Edge {
	VertexId from;
	VertexId to;
	bool isEmpty;
	char symb;
	Edge(VertexId _from, VertexId _to):from(_from), to(_to), isEmpty(true) {}
	
	Edge(VertexId _from, VertexId _to, char _symb):from(_from), to(_to), isEmpty(false), symb(_symb) {}
	Edge(){}
};

struct Node {
	NodeId left, right;
	bool isLetter;
	bool isClass;
	vector <char> allowedSymbols;
	char c;
	NodeId id;
	Node(){}
	Node(NodeId _id, NodeId _left, NodeId _right, bool _isLetter, char _c):id(_id), left(_left), right(_right), isLetter(_isLetter), c(_c), isClass(false) {}
	Node(NodeId _id, const vector <char>& _allowedSymbols):id(_id), left(-1), right(-1), isLetter(false), isClass(true), allowedSymbols(_allowedSymbols) {}
};

typedef vector <Node> Trees;

struct Vertex {
	vector <Edge> edges;
	VertexId id;
	bool isTerminal;
	Vertex(VertexId _id):id(_id),isTerminal(false) {}
	Vertex():isTerminal(false) {}
};

struct Automaton {
	vector <Vertex> vertices;
	VertexId start;
	Automaton(const Node& a) {
		
		assert(a.left == -1 && a.right == -1);
		assert(a.isLetter || a.isClass);
		
		vertices.push_back(Vertex(0));
		vertices.push_back(Vertex(1));
		
		start = 0;
		
		if (a.isLetter) {
			vertices[0].edges.push_back(Edge(0, 1, a.c));
			vertices[1].isTerminal = true;
		}
		else {
			if (a.allowedSymbols.size() == 0) {
				vertices.resize(1);
				vertices[0].isTerminal = true;
			}
			else {
				for (int i = 0; i < a.allowedSymbols.size(); ++i) {
					vertices[0].edges.push_back(Edge(0, 1, a.allowedSymbols[i]));
				}
				vertices[1].isTerminal = true;
			}
		}
	}
	Automaton() {}
};

void copyWithShift(vector <Vertex>& a, const vector <Vertex>&b, int l, int shiftId) {
	for (int i = 0; i < b.size(); ++i) {
		int j = l + i;
		a[j] = b[i];
		a[j].id += shiftId;
		for (int t = 0; t < a[j].edges.size(); ++t) {
			a[j].edges[t].from += shiftId;
			a[j].edges[t].to += shiftId;
		}
	}
}

int getHash(const vector <int>& a) {
	int res = 0;
	for (int i = 0; i < a.size(); ++i)
		res = res * 997 + (a[i] + 1);
	return res;
}

void goEmptyEdges(const Automaton& aut, vector <int>& a) {
	vector <bool> used(aut.vertices.size());
	for (int i = 0; i < a.size(); ++i) {
		used[a[i]] = true;
	}
	
	for (int i = 0; i < a.size(); ++i) {
		int curv = a[i];
		for (int j = 0; j < aut.vertices[curv].edges.size(); ++j) {
			if (aut.vertices[curv].edges[j].isEmpty && !used[aut.vertices[curv].edges[j].to]) {
				a.push_back(aut.vertices[curv].edges[j].to);
				used[aut.vertices[curv].edges[j].to] = true;
			}
		}
	}
	sort(a.begin(), a.end());
}

Automaton makeDeterministic(const Automaton& aut) {
	map <char, int> lib;
	for (int i = 0; i < ALPSIZE; ++i) {
		lib[ALP[i]] = i;
	}

	Automaton result;
	map <int, VertexId> hashes;
	queue < vector <VertexId> > q;
	
	vector <VertexId> start;
	start.push_back(aut.start);
	goEmptyEdges(aut, start);
	q.push(start);
	hashes[getHash(start)] = 0;
	result.start = 0;
	result.vertices.push_back(Vertex(0));
	
	while (!q.empty()) {
		vector <VertexId> cur = q.front();
		q.pop();
		VertexId curId = hashes[getHash(cur)];
		
		for (int i = 0; i < cur.size(); ++i) {
			if (aut.vertices[cur[i]].isTerminal) {
				result.vertices[curId].isTerminal = true;
				break;
			}
		}
		
		vector <VertexId> go[ALPSIZE];
		for (int i = 0; i < cur.size(); ++i) {
			VertexId curv = cur[i];
			for (int j = 0; j < aut.vertices[curv].edges.size(); ++j) {
				if (!aut.vertices[curv].edges[j].isEmpty) {
					go[lib[aut.vertices[curv].edges[j].symb]].push_back(aut.vertices[curv].edges[j].to);
				}
			}
		}
		for (int i = 0; i < ALPSIZE; ++i) {
			go[i].erase(unique(go[i].begin(), go[i].end()), go[i].end());
			sort(go[i].begin(), go[i].end());
			if (go[i].size() == 0) {
				continue;
			}
			goEmptyEdges(aut, go[i]);
			if (hashes.find(getHash(go[i])) == hashes.end()) {
				VertexId newId = result.vertices.size();
				hashes[getHash(go[i])] = newId;
				result.vertices.push_back(Vertex(newId));
				q.push(go[i]);
			}
			VertexId goId = hashes[getHash(go[i])];
			result.vertices[curId].edges.push_back(Edge(curId, goId, ALP[i]));
		}
	}
	return result;
}

Automaton operator ^ (const Automaton& left, const Automaton& right) { //concatenation
	Automaton result;
	result.vertices.resize(left.vertices.size() + right.vertices.size());
	
	copyWithShift(result.vertices, left.vertices, 0, 0);
	copyWithShift(result.vertices, right.vertices, left.vertices.size(), left.vertices.size());
	
	for (int i = 0; i < left.vertices.size(); ++i) {
		if (result.vertices[i].isTerminal) {
			result.vertices[i].isTerminal = false;
			result.vertices[i].edges.push_back(Edge(result.vertices[i].id, right.start + left.vertices.size()));
		}
	}
	result.start = left.start;
	return result;
}

Automaton operator | (const Automaton& left, const Automaton& right) { //alternation
	Automaton result;
	result.vertices.resize(left.vertices.size() + right.vertices.size() + 1);
	
	copyWithShift(result.vertices, left.vertices, 1, 1);
	copyWithShift(result.vertices, right.vertices, 1 + left.vertices.size(), 1 + left.vertices.size());
	
	result.start = 0;
	result.vertices[0] = Vertex(0);
	result.vertices[0].edges.push_back(Edge(0, left.start + 1));
	result.vertices[0].edges.push_back(Edge(0, right.start + 1 + left.vertices.size()));
	return result;
}

Automaton oneOrMore(const Automaton& left) { //one or more
	Automaton result = left;
	for (int i = 0; i < result.vertices.size(); ++i) {
		if (result.vertices[i].isTerminal) {
			result.vertices[i].edges.push_back(Edge(result.vertices[i].id, result.start));
		}
	}
	return result;
}

Automaton zeroOrMore(const Automaton& left) { //zero or more
	Automaton result = oneOrMore(left);
	result.vertices[result.start].isTerminal = true;
	return result;
}

Automaton zeroOrOne(const Automaton &left) { // zero or one
	Automaton result = left;
	result.vertices[result.start].isTerminal = true;
	return result;
}

VertexId getGo(const Automaton& aut, VertexId curId, char c) {
	for (int i = 0; i < aut.vertices[curId].edges.size(); ++i) {
		assert(!aut.vertices[curId].edges[i].isEmpty);
		if (aut.vertices[curId].edges[i].symb == c) {
			return aut.vertices[curId].edges[i].to;
		}
	}
	return -1;
}

pair <int, char> getSymb(const string& s, int pos, bool& error) {
	if (pos >= s.size()) {
		//cerr << "Попытка считать из конца строки" << endl; 
		//cerr << "Program bug" << endl; 
		//!!!!
		//assert(false);
		//!!!!
		error = true;
		return make_pair(-1, 0);
	}
	pair <int, char> result;
	if (s[pos] == '\\') {
		if (pos + 1 < s.size()) {
			result = make_pair(0, s[pos + 1]);
		}
		else {
			//cerr << "После \\ нет символа" << endl;
			cerr << "Wrong regexp format: no symbol found after \\" << endl;
			//!!!!
			//assert(false);
			//!!!!
			error = true;
			result = make_pair(-1, 0);
		}
	}
	else {
		result = make_pair(1, s[pos]);
	}
	
	if (result.first == 1) {
		bool f = false;
		for (int i = 0; i < SPECSIZE; ++i) {
			if (result.second == SPEC[i]) {
				f = true;
				break;
			}
		}
		if (!f) {
			result.first = 0;
		}
	}
	return result;
}

void readSymb(const string& s, int& pos) {
	if (s[pos] == '\\') {
		pos += 2;
	}
	else {
		++pos;
	}
}

NodeId unary(Trees& nodes, const string& s, int& pos, bool& error);
NodeId concatenation(Trees& nodes, const string& s, int& pos, bool& error);
NodeId star(Trees& nodes, const string& s, int& pos, bool& error);

NodeId alternation(Trees& nodes, const string& s, int& pos, bool& error) {
	NodeId result = concatenation(nodes, s, pos, error);
	if (error) {
		return -1;
	}
	while (pos < s.size() && getSymb(s, pos, error) == make_pair(1, '|')) {
		readSymb(s, pos);
		NodeId add = concatenation(nodes, s, pos, error);
		if (error) {
			return -1;
		}
		NodeId newResult = nodes.size();
		nodes.push_back(Node(newResult, result, add, false, '|'));
		result = newResult;
	}
	if (error) {
		return -1;
	}
	return result;
}

NodeId concatenation(Trees& nodes, const string& s, int& pos, bool& error) {
	NodeId result = star(nodes, s, pos, error);
	if (error) {
		return -1;
	}
	while (pos < s.size() && (getSymb(s, pos, error).first == 0 || getSymb(s, pos, error) == make_pair(1, '.') || 
				getSymb(s, pos, error) == make_pair(1, '(') || getSymb(s, pos, error) == make_pair(1, '['))) {
		NodeId add = star(nodes, s, pos, error);
		if (error) {
			return -1;
		}
		NodeId newResult = nodes.size();
		nodes.push_back(Node(newResult, result, add, false, '#'));
		result = newResult;
	}
	if (error) {
		return -1;
	}
	return result;
}

NodeId star(Trees& nodes, const string& s, int& pos, bool& error) {
	NodeId result = unary(nodes, s, pos, error);
	if (error) {
		return -1;
	}
	while (pos < s.size() && (getSymb(s, pos, error) == make_pair(1, '+') || getSymb(s, pos, error) == make_pair(1, '*') ||getSymb(s, pos, error) == make_pair(1, '?'))) {
		NodeId newResult = nodes.size();
		char operation = getSymb(s, pos, error).second;
		nodes.push_back(Node(newResult, result, -1, false, operation));
		readSymb(s, pos);
		result = newResult;
	}
	if (error) {
		return -1;
	}
	return result;
}

NodeId unary(Trees& nodes, const string& s, int& pos, bool& error) { 
	pair <int, char> curSymb = getSymb(s, pos, error);
	if (error) {
		return -1;
	}
	if (curSymb.first == 0) {
		readSymb(s, pos);
		NodeId root = nodes.size();
		nodes.push_back(Node(root, -1, -1, true, curSymb.second));
		return root;
	}
	if (curSymb.first == 1) {
		if (curSymb.second == '(') {
			readSymb(s, pos);
			NodeId root = alternation(nodes, s, pos, error);
			if (error)
				return -1;
			curSymb = getSymb(s, pos, error);
			if (curSymb != make_pair(1, ')')) {
				//!!!!
				//assert(false);
				//!!!!
				//cerr << "Нет закрывающей )" << endl;
				cerr << "Wrong regexp format: expected )" << endl;
				error = true;
				return -1;
			}
			readSymb(s, pos);
			return root;
		}
		if (curSymb.second == '.') {
			readSymb(s, pos);
			vector <char> alp(ALPSIZE);
			for (int i = 0; i < ALPSIZE; ++i) {
				alp[i] = ALP[i];
			}
			NodeId result = nodes.size();
			nodes.push_back(Node(result, alp));
			return result;
		}
		if (curSymb.second == '[') {
			readSymb(s, pos);
			curSymb = getSymb(s, pos, error);
			bool neg = false;
			if (error) {
				return -1;
			}
			if (curSymb == make_pair(1, '^')) {
				neg = true;
				readSymb(s, pos);
				curSymb = getSymb(s, pos, error);
				if (error) {
					return -1;
				}
			}
			
			vector <char> inBrackets;
			while (true) {
				if (curSymb == make_pair(1, ']')) {
					break;
				}
				if (curSymb.first == 1) {
					//!!!!
					//assert(false);
					//!!!!
					cerr << "Wrong regexp format: metacharacter in bracket expression found" << endl;
					//cerr << "Управляющий символ внутри символьного класса" << endl;
					error = true;
					return -1;
				}
				inBrackets.push_back(curSymb.second);
				readSymb(s, pos);
				curSymb = getSymb(s, pos, error);
				if (error) {
					return -1;
				}
			}
			readSymb(s, pos);
			
			vector <char> allowedSymbols;
			
			if (!neg) {
				allowedSymbols = inBrackets;
			}
			else {
				for (int i = 0; i < ALPSIZE; ++i) {
					bool f = true;
					for (int j = 0; j < inBrackets.size(); ++j) {
						if (inBrackets[j] == ALP[i]) {
							f = false;
							break;
						}
					}
					if (f) {
						allowedSymbols.push_back(ALP[i]);
					}
				}
			}
			NodeId result = nodes.size();
			nodes.push_back(Node(result, allowedSymbols));
			return result;
		}
		//!!!!
		//assert(false);
		//!!!!
		cerr << "Program bug\n";
		//cerr << "Попытка считать в качестве выражения какой-то ботвы" << endl;
		error = true;
		return -1;
	}
	assert(false);
}

Automaton buildAutomaton(const vector <Node>& nodes, NodeId v) {
	if (nodes[v].left == -1 && nodes[v].right == -1) {
		return Automaton(nodes[v]);
	}
	else {
		assert(!nodes[v].isLetter && !nodes[v].isClass);
		if (nodes[v].c == '|') { //alternation
			Automaton left = buildAutomaton(nodes, nodes[v].left);
			Automaton right = buildAutomaton(nodes, nodes[v].right);
			return left|right;
		}
		if (nodes[v].c == '#') { //concatenation
			Automaton left = buildAutomaton(nodes, nodes[v].left);
			Automaton right = buildAutomaton(nodes, nodes[v].right);
			return left^right;
		}
		if (nodes[v].c == '+') {
			Automaton left = buildAutomaton(nodes, nodes[v].left);
			return oneOrMore(left);
		}
		if (nodes[v].c == '*') {
			Automaton left = buildAutomaton(nodes, nodes[v].left);
			return zeroOrMore(left);
		}
		if (nodes[v].c == '?') {
			Automaton left = buildAutomaton(nodes, nodes[v].left);
			return zeroOrOne(left);
		}
		cerr << "Program bug" << endl;
		//cerr << "Something in buildAutomaton went wrong" << endl;
		//assert(false);
	}
}

/*void printTree(const vector <Node>& nodes, NodeId v) {
	if (v == -1)
		return ;
	cout << "(";
	printTree(nodes, nodes[v].left);
	cout << nodes[v].c;
	printTree(nodes, nodes[v].right);
	cout << ")"; */
	/*cout << "root: " << root << endl;
	for (int i = 0; i < nodes.size(); ++i) {
		cout << "node " << nodes[i].id << endl;
		if (nodes[i].isLetter)
			cout << "letter " << nodes[i].c << endl;
		else {
			cout << "operation " << nodes[i].c << endl;
		}
		cout << "left " << nodes[i].left << " right " << nodes[i].right << endl << endl;
	}*/
/*}*/

int main(int argc, char* argv[]) {
	if (argc != 4) {
		cerr << "Wrong arguments format\n" << endl;
		return 0;
	}

	ifstream inText(argv[3], std::ifstream::in);
	string pattern;
	int inputType = atoi(argv[1]);
	if (inputType == 1) {
		ifstream inPattern(argv[2], std::ifstream::in);
		inPattern >> pattern;
	}
	else {
		if (inputType == 2) {
			int lengthPattern = strlen(argv[2]);
			pattern.resize(lengthPattern);
			for (int i = 0; i < lengthPattern; ++i) {
				pattern[i] = argv[2][i];
			}
		}
		else {
			cerr << "Wrong arguments format\n" << endl;
			return 0;
		}
	}
	
	if (pattern.size() == 0) {
		cerr << "Wrong regexp format: empty regexp" << endl;
		return 0;
	}
	if (pattern[0] == '+' || pattern[0] == '?' || pattern[0] == '*') {
		cerr << "Wrong regexp format: nothing found before \'+\', \'?\' or \'*\'" << endl;
		return 0;
	}
	Trees nodes;
	bool error = false;
	int pos = 0;
	NodeId root = alternation(nodes, pattern, pos, error);
	if (error) {
		return 0;
	}
	Automaton nfa = buildAutomaton(nodes, root);
	Automaton dfa = makeDeterministic(nfa);
		

	int stringNumber = 0;
	string s;
	while (getline(inText, s)) {
		++stringNumber;
		//string pattern = "a((cc)|(dd))a";
		
		for (int i = 0; i < s.size(); ++i) {
			VertexId curId = dfa.start;
			for (int j = i; j < s.size(); ++j) {
				curId = getGo(dfa, curId, s[j]);
				if (curId == -1) {
					break;
				}
				if (dfa.vertices[curId].isTerminal) {
					cout << "Line: " << stringNumber << " Shift: " << i + 1 << " ";
					for (int t = i; t <= j; ++t) {
						cout << s[t];
					}
					cout << endl;
				}
			}
		}
	}
	return 0;
}
