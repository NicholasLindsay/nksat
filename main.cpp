#include <algorithm>
#include <cassert>
#include <cstdlib>
#include <fstream>
#include <list>
#include <map>
#include <numeric>
#include <sstream>
#include <stack>
#include <vector>

class VarAssignment
{
private:
  //std::map<int,bool> values;
  std::vector<bool> is_assigned;
  std::vector<bool> values;
  int var_count;
public:
  VarAssignment(int c)
    : is_assigned(c+1, false), values(c+1), var_count(c) {}

  /* Returns number of variables */
  size_t NumVars() const
  {
    return var_count;
  }

  /* Returns number of variables */
  int VarCount() const
  {
    return var_count;
  }

  /* Resets object, including changing var_count */
  void Reset(int v)
  {
    is_assigned.clear();
    is_assigned.resize(v+1, false);
    var_count = v; 
  }

  /* Returns true if variable is assigned */
  bool IsAssigned(int v) const
  {
    return is_assigned[v];
  }

  /* Assigns value to variable */
  void AssignVar(int v, bool val)
  {
    is_assigned[v] = true;
    values[v] = val;
  }

  /* Unassigns variable */
  void UnassignVar(int v)
  {
    assert(is_assigned[v]);
    is_assigned[v] = false;
  }

  /* Returns value of variable, or undefined if unassigned. */
  bool VarValue(int v) const
  {
    assert(is_assigned[v]);
    return values[v];
  }

  /* Returns first undefined variable */
  int FirstUnassigned() const
  {
    for (int i = 1; i <= var_count; i++) {
      if (!IsAssigned(i)) return i;
    }
    assert(!"No unassigned variables");
  }

  /* Are variables are assigned */
  bool AllVarAssigned() const
  {
    for (int i = 1; i <= var_count; i++) {
      if (!IsAssigned(i)) return false;
    }
    return true;
  }

  /* String containing list of variables */
  std::string AsString() const
  {
    std::stringstream ss;

    for (int i = 0; i <= var_count; i++) {
      if (is_assigned[i]) {
        if (values[i])
          ss << i;
        else
          ss << -i;
        ss << " ";
      }
    }

    return ss.str();
  }
};

class Clause
{
private:
  int wliterals[2];
  bool in_unsat_list;
  std::list<Clause*>::iterator unsat_list_it;
public:
  std::map<int,bool> literals;
   
  Clause()
    : wliterals {-1,-1}, in_unsat_list(false) {}

  /* Sets watch literal index to value */
  void SetWatchLiteral(int idx, int val)
  {
    assert(wliterals[1-idx] != val);
    wliterals[idx] = val;
  }

  /* Returns watched literal of given index */
  int GetWatchLiteral(int idx)
  {
    return wliterals[idx];
  }

  /* Sets back iterator to unsat list */
  void SetBackIterator(std::list<Clause*>::iterator it)
  {
    assert(in_unsat_list == false);
    unsat_list_it = it;
    in_unsat_list = true;
  }

  /* Returns back iterator for clause */
  std::list<Clause*>::iterator GetBackIterator()
  {
    assert(in_unsat_list == true);
    return unsat_list_it;
  }

  /* Check to see if in unsat list */
  bool InUnsatList()
  {
    return in_unsat_list;
  }

  /* Unset back pointer */
  void UnsetBackIterator()
  {
    assert(in_unsat_list);
    in_unsat_list = false;
  }

  /* Add literal to clause */
  bool AddLiteral(int v, bool negate)
  {
    /* Entry already exists? */
    if (literals.count(v)) {
      /* Contradiction */
      if (literals[v] != negate) return true;
      /* Avoid duplication */
      else return false;
    }
   

    if (wliterals[0] == -1) wliterals[0] = v;
    else                    wliterals[1] = v;

    literals[v] = negate;

    return false;
  }

  /* Evaluates clause for truth under current assignment */
  bool Evaluate(const VarAssignment& m) const
  {
    /* If any variable is true then clause is true. */
    for (auto& literal : literals) {
      if (m.IsAssigned(literal.first) &&
          m.VarValue(literal.first) != literal.second)
        return true;
    }

    return false;
  }

  /* Returns number of decision literals (unassigned vars) in clause */
  int CountDLit(const VarAssignment& m) const
  {
    int unassigned = 0;

    /* Count number of unassigned variables */
    for (auto& literal : literals) {
      if (!m.IsAssigned(literal.first)) unassigned++;
    }

    return unassigned;
  }

  /* Returns first unassigned decision literal. */
  std::pair<int,bool> GetDLit(const VarAssignment& m) const
  {
    for (auto& literal : literals) {
      if (!m.IsAssigned(literal.first)) return literal;
    }
    assert(!"No unassigned literal found");
  }

  /* Returns index of watching clause or -1 if not being watched */
  int WatchingIdx(int var) const
  {
    for (int i = 0; i < 2; i++) {
      if (wliterals[i] == var) return i;
    }
    return -1;
  }

  /* Returns the first unassigned watch variable, or 0 if cannot be found. */ 
  std::pair<int, bool> FindFreshWatch(const VarAssignment& m) const
  {
    // Default return value is 0, false if new watch variable cannot be found
    std::pair<int, bool> retval(0, false);
    bool is_set = false;

    for (const auto& literal : literals) {
      if (literal.first != wliterals[0] && literal.first != wliterals[1]) {
        // Preferentially find a true literal
        if (m.IsAssigned(literal.first) && m.VarValue(literal.first) != literal.second) {
          return literal;
        }
        // Otherwise find an unassigned literal if not yet known
        else if (!is_set && !m.IsAssigned(literal.first)) {
          retval = literal;
          is_set = true;
        }
      }
    }
    
    return retval;
  }

  /* Return watched literal given by index. */
  std::pair<int, bool> GetWatchedLiteral(int idx) const
  {
    assert(0 <= idx && idx < 2);
    return std::pair<int, bool>(wliterals[idx], literals.at(wliterals[idx]));
  }

};

class Solver
{
  /* list of clauses */
  std::vector<Clause> clauses;
  /* list of unsat clauses */
  std::list<Clause*> unsat;
  /* variable assignment */
  VarAssignment m;
  /* sorted list of <variable, sign> of variables */
  std::vector<std::pair<int, bool>> heuristic_list;
  /* per variable, in which clauses is there a poslit */
  std::vector<std::vector<Clause*>> poslits;
  /* per variable, in which clauses is there a neglit */
  std::vector<std::vector<Clause*>> neglits;
private:
  void AddClause(const Clause& c)
  {
    clauses.push_back(c);
  }

public:

  Solver(int c)
    : m(c) {}
    

  void init_lit_lists()
  {
    poslits.resize(m.VarCount() + 1);
    neglits.resize(m.VarCount() + 1);

    for (Clause& clause : clauses) {
      for (const auto& literal : clause.literals) {
        if (literal.second)
          neglits[literal.first].push_back(&clause);
        else
          poslits[literal.first].push_back(&clause);
      }
    }
  }

  void PrintClauses()
  {
    for (const Clause& clause : clauses) {
      for (const auto& literal : clause.literals) {
        if (literal.second) printf("-");
        printf("%d ", literal.first);
      }
      printf ("0\n");
    }
  }

  // Returns true if trivially unsat
  bool LoadFromFile(const char* path)
  {
    int line_no = 0;

    /* Parameters to fill in */
    int nbvar = -1, nbclauses = -1;
    int redundant_clauses = 0;

    /* Load file from path */
    std::ifstream file;

    file.open(path);

    /* Read in lines */
    std::string line;
    while (!file.eof()) {
      getline(file, line);
      line_no++;

      /* Split line into words */
      std::stringstream line_stream(line);
      std::string word;
      line_stream >> word;
      
      /* Comment line */
      if (word == "c") continue;

      /* Settings line */
      else if (word == "p") {
        line_stream >> word;
        assert(word == "cnf");
        line_stream >> nbvar >> nbclauses;
        assert(nbvar > -1);
        assert(nbclauses > -1);
        m.Reset(nbvar);
        continue;
      }

      /* Empty line */
      else if (word == "") continue;

      /* Clause line */
      else {
        Clause clause;
        bool clause_true = false;
        line_stream.seekg(0, std::ios::beg);

        while (!line_stream.eof()) {
          int var;
          line_stream >> var;
          if (line_stream.fail()) {
            printf("Line %d: Syntax error.\n", line_no);
            exit(-1);
          }
          if (var == 0) break;
          if (var > 0) {
            assert (var <= nbvar);
            clause_true = clause.AddLiteral(var, false);
            if (clause_true) break;
          } else {
            assert (-var <= nbvar);
            clause_true = clause.AddLiteral(-var, true);
            if (clause_true) break;
          }
        }

        if (clause_true) {
          redundant_clauses++;
        } else {
          AddClause(clause);
        }
      }
    }

    /* Update watch_list from watch literals */
    for (Clause& clause : clauses) {
      unsat.push_front(&clause);
      clause.SetBackIterator(unsat.begin());
    }

    init_lit_lists();
    
    sort_vars_by_occurence();
   
    //PrintClauses();
    if (trivial_clauses()) return true;

    if (pure_literal_elimination()) return true;

    assert(clauses.size() + redundant_clauses == nbclauses);


    return false;
  }

  /* Removes unwatched clauses from watch_list */
  void remove_unwatched(std::vector<Clause*>& watch_list, 
                        std::vector<Clause*>& remove_list)
  {
    watch_list.erase(
        std::remove_if(watch_list.begin(), watch_list.end(), 
          [&](Clause* el) {
            return (std::find(remove_list.begin(), remove_list.end(), el) 
                != remove_list.end());
          }   
        ),
        watch_list.end()
    );
  }

  enum unit_prop_result {
    UNIT_PROP_RESULT_CONFLICT,   // conflicting terms
    UNIT_PROP_RESULT_UNASSIGNED, // formula contains unassigned variables
    UNIT_PROP_RESULT_OKAY        // formula okay and may be sat
  };
  
  bool pure_literal_elimination()
  {
    std::vector<bool> seen(m.VarCount() + 1, false);
    std::vector<bool> sign(m.VarCount() + 1, false);
    std::vector<bool> impure( m.VarCount() + 1, false);

    for (Clause& clause : clauses) {
      for (const auto& literal : clause.literals) {
        if (!seen[literal.first]) {
          seen[literal.first] = true;
          sign[literal.first] = literal.second;
        }
        else {
          if (sign[literal.first] != literal.second) {
            impure[literal.first] = true;
          }
        }
      }
    }
    
    // dummy for unit_prop
    std::vector<int> assigned_vars;
    std::vector<Clause*> unsat_vals;

    for (int i = 1; i <= m.VarCount(); i++) {
      if (!impure[i]) {
        //m.AssignVar(i, !sign[i]);
        // clear dummy vectors
        assigned_vars.clear();
        unsat_vals.clear();
        auto res = unit_prop(assigned_vars, i, !sign[i], unsat_vals);
        assert(res != UNIT_PROP_RESULT_CONFLICT);
        if (res == UNIT_PROP_RESULT_CONFLICT) return true;
      }
    }

    return false;
  }


  std::pair<int, bool> next_unassigned(int* last_pos)
  {
    for (int i = *last_pos; i < heuristic_list.size(); i++) {
      const auto& entry = heuristic_list[i];
      if (!m.IsAssigned(entry.first)) {
        *last_pos = i;
        return entry;
      }
    }
    assert(!"No unassigned variables!");
  }

  void sort_vars_by_occurence()
  {
    std::vector<int> total_occ(m.VarCount() + 1, 0);
    std::vector<int> pos_occ(m.VarCount() + 1, 0);

    for (Clause& clause : clauses) {
      for (const auto& literal : clause.literals) {
        total_occ[literal.first]++;
        if (!literal.second)
          pos_occ[literal.first]++;
      }
    }

    std::vector<int> idxs(m.VarCount() + 1);
    std::iota(idxs.begin(), idxs.end(), 0);

    std::sort(idxs.begin(), idxs.end(),
       [&total_occ](int i1, int i2) {return total_occ[i1] > total_occ[i2];}); 

    for (int idx : idxs) {
      if (idx == 0) continue;
      bool pos = (pos_occ[idx] > total_occ[idx] - pos_occ[idx]);
      heuristic_list.push_back(std::pair<int, bool>(idx, pos));
    }
  }

  bool trivial_clauses()
  {
    // dummy for unit_prop
    std::vector<int> assigned_vars;
    std::vector<Clause*> unsat_vals;

    for (Clause& clause : clauses) {
      if (clause.literals.size() == 1) {
        assigned_vars.clear();
        unsat_vals.clear();

        auto it = clause.literals.begin();
        const auto& literal = *it;
        auto res = unit_prop(assigned_vars, literal.first, !literal.second, unsat_vals);
        if (res == UNIT_PROP_RESULT_CONFLICT) {
          return true;
        }
      }
    }

    return false;
  }

  /*
   * Performs unit propation and returns true if a conflict is detected.
   *
   * Every clause is evaluated with the current variable assignment m. If the
   * clause is unsatisfied, then it MAY be a contradiction or a unit clause,
   * at which point unit progagation can be applied. If the number of
   * unassigned literals is 0, then the unit propogations led to a
   * contradiction. 
   */
  unit_prop_result unit_prop(std::vector<int>& assigned_vars, int var, bool val, 
                             std::vector<Clause*>& unsat_vals)
  {
    static std::vector<std::pair<int, bool>> unit_prop_vars;

    static std::vector<decltype(unsat)::iterator> unsat_its;

    unit_prop_vars.clear();
    unsat_its.clear();

    unit_prop_vars.push_back(std::pair<int, bool>(var, val));

    // watch variables that are unassigned
    std::vector<bool> unassign_map(m.NumVars() + 1, false);
    int unassign_cnt = 0;
   
    for (int i = 0; i < unit_prop_vars.size(); i++) {
      const std::pair<int, bool>&assign = unit_prop_vars[i];   
    //for (const std::pair<int, bool>& assign : unit_prop_vars) {
      var = assign.first;
      val = assign.second;
      
      // Has variable been assigned to opposite value?
      if (m.IsAssigned(var)) {
        if (m.VarValue(var) == !val) {
          // conflict
          return UNIT_PROP_RESULT_CONFLICT;
        } else {
          // already assigned
          continue;
        }
      }

      // Assign variable
      m.AssignVar(var, val);
      assigned_vars.push_back(var);

      // Mark variable as assigned if previously unassigned
      if (unassign_map[var]) {
        unassign_map[var] = false;
        unassign_cnt--;
        assert(unassign_cnt >= 0);
      }

      // Mark all clauses which are now true
      auto& true_list = (assign.second) ? poslits[assign.first] : neglits[assign.first];
      for (auto clause : true_list) {
        if (clause->InUnsatList()) {
          unsat.erase(clause->GetBackIterator());
          unsat_vals.push_back(clause);
          clause->UnsetBackIterator();
        }
      }

      // Look through all false clauses
      auto& false_list = (assign.second) ? neglits[assign.first] : poslits[assign.first];

      // Find clauses which are watching var
      for (Clause* clause : false_list) {
        int watching_idx = clause->WatchingIdx(var);

        // variable is not being watched by this clause
        if (watching_idx == -1) continue;

        // Variable must be watched
        assert(watching_idx != -1);

        // Find another literal to watch
        std::pair<int, bool> fresh = clause->FindFreshWatch(m); 

        // Couldn't find another literal
        if (fresh.first == 0) {
          // Clause is false ==> unit prop other watched literal
          // If clause only contains 1 literal then we have a contradiction
          if (clause->GetWatchLiteral(1) == -1) {
            return UNIT_PROP_RESULT_CONFLICT;
          }

          // Find the other watched literal that we need to propagate
          std::pair<int,bool> other_watched_literal;
          other_watched_literal = clause->GetWatchedLiteral(1 - watching_idx);
          
          // Clause can be true if other watch literal is true
          if (m.IsAssigned(other_watched_literal.first) && (
              other_watched_literal.second != m.VarValue(other_watched_literal.first))) continue;

          // Assign this literal to true
          std::pair<int,bool> assignment;
          assignment.first = other_watched_literal.first;
          assignment.second = !other_watched_literal.second;

          unit_prop_vars.push_back(assignment);
        } else { // Found another literal
          clause->SetWatchLiteral(watching_idx, fresh.first);
          
          // if new watch literal is unassigned then don't need to do sat
          // check unless it becomes assigned.
          if (!m.IsAssigned(fresh.first) && !unassign_map[fresh.first]) {
            unassign_map[fresh.first] = true;
            unassign_cnt++;
          } else {
            // is new watched literal true
            if (m.IsAssigned(fresh.first) && 
                m.VarValue(fresh.first) != fresh.second) {
              if (clause->InUnsatList()) {
                unsat_vals.push_back(clause);
                unsat.erase(clause->GetBackIterator());
                clause->UnsetBackIterator();
              }
            }
          }
        } 
      }
    }

    /* Unassigned watch variables */
    if (unassign_cnt > 0)
      return UNIT_PROP_RESULT_UNASSIGNED;
    /* No conflicts */
    else
      return UNIT_PROP_RESULT_OKAY;
  }

  void unassign_vars(const std::vector<int>& vars)
  {
    for (int var : vars) m.UnassignVar(var);
  }

  bool is_sat(int last_pos) 
  {
    /* Variables assigned by unit prop */
    std::vector<int> assigned_vars;

    /* Clauses which were satisfied by this function */
    std::vector<decltype(unsat)::iterator> unsat_its;
    std::vector<Clause*> unsat_vals;

    /* Is sat */
    if (unsat.size() == 0) return true;
    
    if (last_pos == m.VarCount() - 1) {
      printf("Error: unsat clauses with no more vars to assign\n");
      exit(0);
    }
    
    /* Update unsat list */
    for (auto it : unsat_its) {
      unsat.erase(it);
    }

    /* Newly sat clauses by unit prop */
    std::vector<Clause*> up_unsat_vals;

    /* Decision */
    auto i = next_unassigned(&last_pos);
    
    /* i = true case */
    unit_prop_result res = unit_prop(assigned_vars, i.first, i.second, up_unsat_vals);
  
    switch (res) {
    case UNIT_PROP_RESULT_CONFLICT:
        break;
    case UNIT_PROP_RESULT_UNASSIGNED:
        if (is_sat(last_pos)) return true;
        break;
    default: // fallthrough
    case UNIT_PROP_RESULT_OKAY:
        if (is_sat(last_pos)) return true;
        break;
    }

    unassign_vars(assigned_vars);
    assigned_vars.clear();
    
    for (auto val : up_unsat_vals) {
      unsat.push_front(val);
      val->SetBackIterator(unsat.begin());
    }
    up_unsat_vals.clear();
   
    /* i = false case */ 
    res = unit_prop(assigned_vars, i.first, !i.second, up_unsat_vals);

    switch (res) {
    case UNIT_PROP_RESULT_CONFLICT:
        break;
    case UNIT_PROP_RESULT_UNASSIGNED:
        if (is_sat(last_pos)) return true;
        break;
    default: // fallthrough
    case UNIT_PROP_RESULT_OKAY:
        if (is_sat(last_pos)) return true;
        break;
    }

    unassign_vars(assigned_vars);

    /* Reinstall unsat log */
    for (auto val : up_unsat_vals) {
      unsat.push_front(val);
      val->SetBackIterator(unsat.begin());
    }
    for (auto val : unsat_vals) {
      unsat.push_front(val);
      val->SetBackIterator(unsat.begin());
    }

    return false; 
  }

  const VarAssignment& GetAssignments() const
  {
    return m;
  }
};

int main(int argc, char** argv)
{

  /* Validate input */
  if (argc != 2) {
    fprintf(stderr, "Invalid input. Expected %s <cnf file>\n", argv[0]);
    return -1;
  }

  Solver sat(0);
  fprintf(stderr, "Starting nksat!\n");

  /* File can be invalid. */  
  if (sat.LoadFromFile(argv[1])) {
    printf("Unsatisfiable!\n");
    return 0;
  }

  if (sat.is_sat(0)) {
    printf("Satisfiable!\n");
    printf("Assignments: %s\n", sat.GetAssignments().AsString().c_str());
  } 
  else {
    printf("Unsatisfiable!\n");
  }

  return 0;
}

