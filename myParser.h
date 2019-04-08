#ifndef MY_PARSER_H
#define MY_PARSER_H

#include <iostream>
#include <cstdlib>
#include <string>
#include <vector>
#include "Token.h"
#include "DatalogProgram.h"
#include "Parameter.h"
#include "Predicate.h"
#include "Rule.h"

using namespace std;

// scans input string
class myParser{
private:
  vector<Token> v; //vector of Tokens passed in from myScanner
  vector<Token> v2;
  int i;
  Token tok;
  Predicate dom;
  bool worked;

  //Parameter Grammars
  void parameter(Predicate *pred);
  void expression(Predicate *pred);
  void op(Predicate *pred);

  //Parameter Grammars
  void parameterList(Predicate *pred);
  void stringList(Predicate *pred);
  void idList(Predicate *pred);

  //Higher Predicate Lists
  void schemeList(Predicate *pred);
  void factList(Predicate *pred);
  void ruleList(Predicate *pred);
  void queryList(Predicate *pred);

  //Higher Predicate Grammars
  void scheme(Predicate *pred);
  void fact(Predicate *pred);
  void rule(Predicate *pred);
  void query(Predicate *pred);

  //Predicate Grammars
  Predicate headPredicate();
  void predicate(Predicate *pred);
  Predicate predicate2();
  void predicate_Q(Predicate *pred);
  void predicate_VoP(vector<Predicate> *VoP);

  //Predicate Lists
  void predicateList(Predicate *pred);
  void predicateList_VoP(vector<Predicate> *VoP);

  //Primary Driving Functions
  void remove_comments();
  void catchErrors();
  DatalogProgram datalogProgram();

  //Supporting Functions
  void match(int type);
  void add_domain(string in);
  void error();

public:
  //Constructor
  myParser(vector<Token> in);
  bool success();
  vector<Token> getTokens();

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

#endif
