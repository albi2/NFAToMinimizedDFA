#include <iostream>
#include <string>
#include <iomanip>
#include <map>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <queue>
#include <algorithm>
#define MAX_SIZE 100

const int symbols_no = 2;
/*
- ADD FUNCTIONALITY FOR MAPPING THE SYMBOLS TO NUMBERS
- ADD READING FROM FILES
- ADD MINIMIZATION
- FACTOR CODE
*/

// Set array elements to zero
void make_zero(int arr[], int size) {
	for (int i = 0; i < size; i++)
		arr[i] = 0;
}

// Function to update the map the states that have been reached using E-closures
void updateMap(std::map<char, int>& closure_buffer,const std::string& closures) {	
	for (int i = 0; i < closures.length(); i++) {
		if (closure_buffer.find(closures[i]) == closure_buffer.end())
			closure_buffer[closures[i]] = 1;
	}
}

// Returns the next state whose closure has not been considered yet
int nextState(std::map<char, int>& closure_buffer) {
	std::map<char, int>::iterator it;
	for (it = closure_buffer.begin(); it != closure_buffer.end(); ++it) {
		if (it->second == 1)
			return (int)(it->first)-65;
	}

	return -1;
}

// Turns the closure into a string
std::string getClosure(std::map<char, int>& closure_buffer) {
	std::string closure = "";
	std::map<char, int>::iterator it;
	for (it = closure_buffer.begin(); it != closure_buffer.end(); ++it)
		closure += it->first;
	return closure;
}

// Function that takes and displays/stores all epsilon closures for 
// each state of the NFA
void DisplayEpsilonClosures(int states,
	std::string closures[], std::string NFA_TABLE[][symbols_no+1]) {
	
	std::map<char, int> closure_buffer;

	for (int i = 0; i < states; i++) {
		closure_buffer[static_cast<char>(i+65)] = 2;

		if ( NFA_TABLE[i][symbols_no] != "-" ) {
			std::string current = NFA_TABLE[i][symbols_no];
			updateMap(closure_buffer, current);

			int current_state = nextState(closure_buffer);

			while (current_state != -1) {

				if (NFA_TABLE[current_state][symbols_no] != "-") {
					current = NFA_TABLE[current_state][symbols_no];
					updateMap(closure_buffer, current);
				}
				closure_buffer[char(current_state + 65)]++;
				current_state = nextState(closure_buffer);

			}
		}

		std::cout << "E-Closure ( " << char(i + 65) << " ) : ";
		std::string closure = getClosure(closure_buffer);
		closures[i] = closure;
		std::cout << closure << std::endl;
		closure_buffer.clear();
	}
}

//std::unordered_set<char> getSetFromString(const std::string& states) {
//	std::unordered_set<char> set;
//	set.insert(states.begin(), states.end());
//	return set;
//}

std::string getStringFromSet(const std::set<char>& states) {
	std::string result = "";
	if (!states.empty()) result.insert(result.begin(), states.begin(), states.end());
	else result = "-";
	return result;
}

std::set<char> transition(const std::string& dfa_state, 
	std::string NFA_TABLE[][symbols_no+1], int symbol, std::string closures[]) {
	std::set<char> transition_state;
	// Find transition state through symbol for given state
	if(dfa_state != "-")
		for (char c : dfa_state) {
			if (NFA_TABLE[(int)c - 65][symbol] != "-") {
				std::string transitions = NFA_TABLE[(int)c - 65][symbol];
				transition_state.insert(transitions.begin(), transitions.end());
			}
		}
	// Convert to string so you can get closure for every state
	std::string tr_state = getStringFromSet(transition_state);
	// Find E-Closure of the given transition
	if(tr_state  != "-")
		for (char c : tr_state) {
			std::string closure = closures[(int)c - 65];
			if (closure != "-") {
				transition_state.insert(closure.begin(), closure.end());
			}
		}

	return transition_state;
}

bool isFinalState(const std::string& dfa_state, int final_states[]) {
	if (dfa_state == "-")
		return false;

	for (char c : dfa_state) {
		if (final_states[(int)c - 65] == 1)
			return true;
	}
	return false;
}

// Removing unreachable states from a DFA using BFS
std::string** RemoveUnreachable(std::string DFA_TABLE[][symbols_no],
	std::unordered_map<std::string, int> states_container, int& new_size) {

	// Initialize the visited array
	int* visited = new int[states_container.size()];
	make_zero(visited, states_container.size());
	visited[0] = true;
	new_size = 1;

	std::queue<int> q;
	q.push(0);

	while (!q.empty()) {
		int current_state = q.front();
		q.pop();
		for (int i = 0; i < symbols_no; i++) {
			int reachable_state = states_container[DFA_TABLE[current_state][i]];
			if (!visited[reachable_state]) {
				q.push(reachable_state);
				visited[reachable_state] = 1;
				++new_size;
			}
		}
	}

	std::string** new_DFA_Table = new std::string * [new_size];
	for (int i = 0; i < new_size; i++) {
		new_DFA_Table[i] = new std::string[symbols_no];
	}

	for (int i = 0; i < new_size; i++) {
		if(visited[i])
			for (int j = 0; j < symbols_no; j++) {
				new_DFA_Table[i][j] = DFA_TABLE[i][j];
			}
	}
	delete[] visited;

	return new_DFA_Table;
}

std::string getDFAStateFromSet(std::set<int> S, std::unordered_map<int, std::string> number_to_state) {
	std::set<std::string> state;

	for (int dfa_state : S) {
		state.insert(number_to_state[dfa_state]);
	}

	std::string stateString = "";
	for (const std::string& s : state)
		stateString += s + ",";
	stateString.pop_back();

	return stateString;
}

// 
void AddToMinimizedTable(std::string** Minimized_DFA_Table, std::string** DFA_TABLE,  std::set<int>& S,
	 std::unordered_map<int, std::string>& number_to_state, std::vector<std::set<int>>& P,
	std::unordered_map<std::string,int> states_container, std::unordered_map<std::string, int> new_states_container) {


	for (int i = 0; i < symbols_no; i++) {
		std::set<int> reachingState;
		for (int previousState : S) {
			reachingState.insert(states_container[DFA_TABLE[previousState][i]]);
		}
		
		std::string reachingStateString = "";
		for (std::set<int> set : P) {
			if (std::includes(set.begin(), set.end(), reachingState.begin(), reachingState.end())) {
				reachingStateString = getDFAStateFromSet(set, number_to_state);
				break;
			}
		}

		Minimized_DFA_Table[new_states_container[getDFAStateFromSet(S, number_to_state)]][i] = reachingStateString;
	}
}


std::string** MinimizeDFA(std::string** DFA_TABLE, std::unordered_map<std::string, int>& states_container,
	const int* final_states, int& theSize, std::unordered_map<int, std::string>& number_to_state,
	std::unordered_map<int, std::string>& new_number_to_state, std::unordered_set<int>& new_final_states) {

	std::vector<std::set<int>> P(2);
	std::vector<std::set<int>> W(2);

	for (int i = 0; i < states_container.size(); i++) {
		P[!final_states[i]].insert(i);
		W[!final_states[i]].insert(i);
	}


	while (!W.empty()) {
		std::set<int> A = W.front();
		W.erase(W.begin());

		for (int i = 0; i < symbols_no; i++) {
			// X - set of states for which a transition on symbol i leads to state in A
			std::set<int> X;
			for (int j = 0; j < states_container.size(); j++) {
				if (A.find(states_container[DFA_TABLE[j][i]]) != A.end()) {
					X.insert(j);
				}
			}

			std::vector<std::set<int>> P_copy;
			for (std::set<int>& s : P)
				P_copy.push_back(s);
			for (std::set<int>& Y : P_copy) {

				std::set<int> x_y_intersection;
				std::set_intersection(X.begin(), X.end(), Y.begin(), Y.end(), std::inserter(x_y_intersection,x_y_intersection.begin()));

				std::set<int> x_y_difference;
				std::set_difference( Y.begin(),Y.end() , X.begin(), X.end(), std::inserter(x_y_difference, x_y_difference.begin()));

				if (x_y_intersection.empty() || x_y_difference.empty()) continue;

				P.erase(std::find(P.begin(), P.end(), Y));
				P.push_back(x_y_intersection);
				P.push_back(x_y_difference);

				if (std::find(W.begin(), W.end(), Y) != W.end()) {
					W.erase(std::find( W.begin(), W.end(), Y ));
					W.push_back( x_y_intersection );
					W.push_back( x_y_difference );
				} else {
					if (x_y_intersection.size() <= x_y_difference.size()) {
						W.push_back(x_y_intersection);
					}
					else W.push_back(x_y_difference);
				}
			}
		}
	}

	int current_position = 0;

	std::set<int> initialState;
	for (int i = 0; i < P.size(); i++) {
		if (P[i].find(0) != P[i].end()) {
			initialState = P[i];
			break;
		}
	}

	std::unordered_map<std::string, int> new_states_container;
	for (int c : initialState) {
		if (final_states[c] == 1) {
			new_final_states.insert(current_position);
			break;
		}
	}
	new_number_to_state[current_position] = getDFAStateFromSet(initialState, number_to_state);
	new_states_container[getDFAStateFromSet(initialState, number_to_state)] = current_position++;

	for (std::set<int> state : P) {
		if (state == initialState) continue;
		std::string current_state = getDFAStateFromSet(state, number_to_state);

		for (int c : state) {
			if (final_states[c] == 1) {
				new_final_states.insert(current_position);
				break;
			}
		}
		new_number_to_state[current_position] = current_state;
		new_states_container[current_state] = current_position++;
	}

	std::string** Minimized_DFA_Table = new std::string*[P.size()];
	for (int i = 0; i < P.size(); i++) {
		Minimized_DFA_Table[i] = new std::string[symbols_no];
	}

	theSize = P.size();

	AddToMinimizedTable(Minimized_DFA_Table, DFA_TABLE,  initialState,  number_to_state, P, states_container, new_states_container);

	for (std::set<int> S : P) {
		if (S == initialState) continue;

		AddToMinimizedTable(Minimized_DFA_Table, DFA_TABLE, S, number_to_state, P, states_container, new_states_container);
	}

	return Minimized_DFA_Table;
}


int main() {
	const int states_no = 7;

	std::string NFA_TABLE[states_no][symbols_no + 1];
	std::string DFA_TABLE[MAX_SIZE][symbols_no];

	std::cout << "STATES :  ";
	for (int i = 0; i < states_no; i++)
		std::cout << static_cast<char>(i + 65) << " ";
	std::cout << std::endl;

	std::cout << "\n" << "SYMBOLS :  ";
	for (int i = 0; i < symbols_no; i++)
		std::cout << i << "  ";
	std::cout << "E" << std::endl << std::endl;

	NFA_TABLE[0][0] = "-";
	NFA_TABLE[0][1] = "-";
	NFA_TABLE[0][2] = "BD";
	NFA_TABLE[1][0] = "C";
	NFA_TABLE[1][1] = "B";
	NFA_TABLE[1][2] = "-";
	NFA_TABLE[2][0] = "B";
	NFA_TABLE[2][1] = "C";
	NFA_TABLE[2][2] = "-";
	NFA_TABLE[3][0] = "E";
	NFA_TABLE[3][1] = "D";
	NFA_TABLE[3][2] = "-";
	NFA_TABLE[4][0] = "G";
	NFA_TABLE[4][1] = "F";
	NFA_TABLE[4][2] = "-";
	NFA_TABLE[5][0] = "E";
	NFA_TABLE[5][1] = "F";
	NFA_TABLE[5][2] = "-";
	NFA_TABLE[6][0] = "G";
	NFA_TABLE[6][1] = "G";
	NFA_TABLE[6][2] = "-";

	// Final states
	int final_states[states_no];
	make_zero(final_states, states_no);
	// Set final state to 1
	final_states[0] = 1;
	final_states[2] = 1;
	final_states[3] = 1;
	final_states[4] = 1;
	final_states[6] = 1;

	std::cout << "STATES    ";
	for (int i = 0; i < symbols_no; i++)
		std::cout << std::setw(10) << i;
	std::cout << std::setw(10) << "E" << std::endl;

	for (int i = 0; i < states_no; i++) {
		std::cout << std::setw(10) << std::left << static_cast<char>(i + 65);
		std::cout << std::right;
		for (int j = 0; j < symbols_no + 1; j++) {
			std::cout << std::setw(10) << NFA_TABLE[i][j];
		}
		std::cout << std::endl;
	}

	std::string closures[states_no];
	for (int i = 0; i < states_no; i++) closures[i] = "-";
	std::cout << "\n--------------- EPSILON CLOSURES ---------------\n" << std::endl;
	DisplayEpsilonClosures(states_no, closures, NFA_TABLE);

	int current_dfa_state = 0;


	// Mapping indexes to states
	std::unordered_map<int, std::string> numberToState;

	// States are gonna be in the form of sets  to avoid duplication, and stored as strings
	std::unordered_map<std::string, int> states_container;
	std::queue<std::string> states;

	// First state logistics
	states_container[closures[0]] = current_dfa_state;

	numberToState[current_dfa_state++] = closures[0];
	states.push(closures[0]);

	while (!states.empty()) {
		std::string current_state_string = states.front();
		states.pop();

		for (int i = 0; i < symbols_no; i++) {
			std::set<char> new_state = transition(current_state_string, NFA_TABLE, i, closures);
			std::string new_state_string = getStringFromSet(new_state);

			if (states_container.find(new_state_string) == states_container.end()) {
				states_container[new_state_string] = current_dfa_state;
				states.push(new_state_string);

				// Map numbers to string states
				numberToState[current_dfa_state++] = new_state_string;
			}
			DFA_TABLE[states_container[current_state_string]][i] = new_state_string;
		}
	}

	//// ANOTHER DFA WHICH NEEDS MINIMIZATION
	//std::string DFA_TABLE[states_no][symbols_no];
	//DFA_TABLE[0][0] = "B";
	//DFA_TABLE[0][1] = "C";
	//DFA_TABLE[1][0] = "A";
	//DFA_TABLE[1][1] = "D";
	//DFA_TABLE[2][0] = "E";
	//DFA_TABLE[2][1] = "F";
	//DFA_TABLE[3][0] = "E";
	//DFA_TABLE[3][1] = "F";
	//DFA_TABLE[4][0] = "E";
	//DFA_TABLE[4][1] = "F";
	//DFA_TABLE[5][0] = "F";
	//DFA_TABLE[5][1] = "F";

	//std::unordered_map<std::string, int> states_container = {
	//	{"A", 0},
	//	{"B", 1},
	//	{"C", 2},
	//	{"D", 3},
	//	{"E", 4},
	//	{"F", 5}
	//};

	//int final_states[] = { 0, 0, 1, 1, 1, 0 };

	//std::unordered_map<int, std::string> numberToState = {
	//	{0, "A"},
	//	{1, "B"},
	//	{2, "C"},
	//	{3, "D"},
	//	{4, "E"},
	//	{5, "F"}
	//};

	int* dfa_final_states = new int[states_container.size()];
	std::unordered_map<std::string, int>::iterator it;
	for (it = states_container.begin(); it != states_container.end(); it++) {
		if (isFinalState(it->first, final_states))
			dfa_final_states[it->second] = 1;
		else dfa_final_states[it->second] = 0;
	}

	// Size after removing the unreachable states of the DFA
	int m_size = 0;
	std::string** DFA_TABLE_m = RemoveUnreachable(DFA_TABLE, states_container, m_size);

	/*std::cout << "\n\n--------------------- DFA TABLE BEFORE MINIMIZATION ------------------" << std::endl;

	std::cout << "\nSTATES    ";
	for (int i = 0; i < symbols_no; i++)
		std::cout << std::setw(10) << i;
	std::cout << std::endl;

	for (int i = 0; i < m_size; i++) {
		std::cout << std::setw(10) << std::left << numberToState[i];
		std::cout << std::right;
		for (int j = 0; j < symbols_no; j++) {
			std::cout << std::setw(10) << DFA_TABLE_m[i][j];
		}
		std::cout << std::endl;
	}

	std::cout << std::endl << "---------------------- FINAL DFA STATES --------------------" << std::endl;
	for (int i = 0; i < states_container.size(); i++) {
		if (dfa_final_states[i])
			std::cout << numberToState[i] << std::endl;
	}*/

	std::unordered_map<int, std::string> new_number_to_state;
	std::unordered_set<int> new_final_states;
	DFA_TABLE_m = MinimizeDFA(DFA_TABLE_m, states_container, dfa_final_states, m_size, numberToState, new_number_to_state, new_final_states);

	std::cout << "\n\n--------------------- DFA TABLE ------------------" << std::endl;

	std::cout << "\nSTATES    ";
	for (int i = 0; i < symbols_no; i++)
		std::cout << std::setw(10) << i;
	std::cout << std::endl;

	for (int i = 0; i < m_size; i++) {
		std::cout << std::setw(10) << std::left << new_number_to_state[i];
		std::cout << std::right;
		for (int j = 0; j < symbols_no; j++) {
			std::cout << std::setw(10) << DFA_TABLE_m[i][j];
		}
		std::cout << std::endl;
	}

	std::cout << std::endl << "---------------------- FINAL DFA STATES --------------------" << std::endl;
	for (int c : new_final_states) 
		std::cout << new_number_to_state[c] << std::endl;
	
}