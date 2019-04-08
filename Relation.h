#pragma once

#include <iostream>
#include <cstdlib>
#include <string>
#include <set>
#include <map>
#include <vector>
#include "Scheme.h"
#include "Tuple.h"

using namespace std;

class Relation{
private:
  string name; //name of relation
  Scheme sch; //contains list of scheme attributes
  Tuple que; //contains the query being assessed, for interpreter (because renames/projects change scheme), not database
  Scheme sch2;
  set<Tuple> tup; //set of tuples
  set<Tuple>::iterator it; //iterator for navigating through set of tuples
  int order;

public:
  //Constructors
  Relation();
  Relation(string name_in, Scheme &sch_in);
  Relation(string name_in, Scheme &sch_in, int order_in);
  Relation(string name_in, Scheme &sch_in, set<Tuple> &tup_in);

  //Push Functions
  void changename(string in); //changes the name(data member) of the Relation
  void addTuple(Tuple &t); //Adds new Tuple to relation
  void addQuery(Tuple &q); //returns contents of query
  void addScheme2(vector<string> in);
  void addOrder(int order_in);

  //Pull Functions
  string getName(); //Returns name of Relation
  int getSize(); //returns number of tuples in the relation
  vector<string> getQuery(); //returns contents of query
  vector<string> getScheme();
  Scheme getScheme_s();
  vector<string> getScheme2();
  void print(); //prints out relation, unformatted
  void print_cerr();
  void print_output_q(); //prints out relation, formatted for Query Interpreter
  void print_output_r(); //prints out relation, formatted for Rule Interpreter
  set<Tuple> getTuples();

  //Relational Operations
  Relation select_pv(int position, string value); //Finds tuples that have value at position, for assessing constants
  Relation select_pp(vector<int> positions); //Finds tuples that have same value at specified positions, for assessing variables
  Relation project(vector<int> positions); //projects relation according to the positions vector

  Scheme project_scheme(vector<int> &positions); //rearranges scheme according to positions vector, assists project()
  Relation rename(Scheme &in); //replaces the scheme with inputed one
  Relation join(Relation &in);
  Scheme combineSchemes(vector<string> v1, vector<string> v2);
  vector<string> combineWithDuplicates(vector<string> v1, vector<string> v2);
  Tuple combineTuples(vector<string> &v1, vector<string> &v2);
  Relation unionize(Relation &in);
  map<string,vector<int>>checkSameness(vector<string> &t_vec);
  vector<int> removeDuplicates_pos(vector<string> &in);
  Relation cartesianProduct(Relation &in);

  bool operator <(const Relation &right) const{//Compares Tuples by vectors, used for ordering Tuples in a set
    return order < right.order;
  }
};
