#pragma once

#include <iostream>
#include <cstdlib>
#include <string>
#include <sstream>
#include <vector>
#include <map>
#include "Token.h"
#include "myParser.h"
#include "Database.h"
#include "Relation.h"
#include "Scheme.h"
#include "Tuple.h"

using namespace std;

class myInterpreter{
private:
  vector<Token> v;
  int i;
  Database db;
  vector<Relation> output_q;
//  vector<Relation> output_r;
  vector<string> rule_list;
  map<Relation,set<Relation>> mapofrules;
  map<string, Relation>::iterator mmit;


public:
  //Constructor
  myInterpreter(vector<Token> &v_in);

  //Database
  void readin(); //Reads Tokens into the Database
  void readschemes(); //Creates Relations from Schemes, called by readin()
  void readfacts(); //Creates Tuples from Facts, adds Tuples to appropriate Relation, called by readin()

  //Rule Interpreter
  void readrules(); //Skips past all rules, called by readin()
  void fixedpoint();
  vector<int> getPositions4project(vector<string> hp, vector<string> p);
  //void print_rules_done(int &passes);
  void print_rules(set<Relation> &output_r);

  //Query Interpreter
  void readqueries(); //Reads in queries, assesses them, and stores product in output vector, called by readin()
  Relation assessquery(Tuple &t, Relation &r); //runs relational operators on a query, assists readqueries()
  map<string, vector<int>> checkSameness(Tuple &t); //evaluates common parameters in aquery, assists assessquery()
  vector<int> varPositions(vector<string> vsch); //finds and returns position of variables within a query, assists assessquery()
  //vector<string> removeDuplicates(vector<string> in); //removes duplicates in vector of strings, assists projection stage in assessquery()
  vector<int> removeDuplicates_pos(vector<string> in); //returns positions of vector without duplicates, assists projection stage in assessquery()
  void print_query(); //iterates through output vector and format-prints each Relation, called by readin()

  //Tokentype Enum
  enum Tokentype{
    _comma,
    _period,
    _q_mark,
    _left_paren,
    _right_paren,
    _colon,
    _colon_dash,
    _multiply,
    _add,
    _schemes,
    _facts,
    _rules,
    _queries,
    _id,
    _string,
    _comment,
    _undefined,
    _eof
  };
};
