#include "DatalogProgram.h"

DatalogProgram::DatalogProgram(string in_s, string in_f, string in_r, string in_q, string in_d){//Parameterized Constructor
  str_schemes = in_s;
  str_facts = in_f;
  str_rules = in_r;
  str_queries = in_q;
  str_domain = in_d;
  success = "Success!\n";
}

DatalogProgram::DatalogProgram(){//Unparameterized Constructor
  str_schemes = "";
  str_facts = "";
  str_rules = "";
  str_queries = "";
  str_domain = "";
  success = "Success!\n";
}

void DatalogProgram::output(){//Formats and executes output string
  string out = success + str_schemes + str_facts + str_rules + str_queries + str_domain;
  cout << out;
}
