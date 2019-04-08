#pragma once

#include <iostream>
#include <cstdlib>
#include <string>

using namespace std;

class DatalogProgram
{
private:
  string success; //"Success!" string

  //Higher predicate strings
  string str_schemes;
  string str_facts;
  string str_rules;
  string str_queries;
  string str_domain;

public:
  DatalogProgram(string in_s, string in_f, string in_r, string in_q, string in_d);
  DatalogProgram();
  void output();
};
