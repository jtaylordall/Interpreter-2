#include "Rule.h"

Rule::Rule(){//Unparameterized Constructor
  headP = "";
}

Rule::Rule(string in_headP){//Parameterized Constructor
  headP = in_headP;
}

void Rule::addPred(string in_pred){//Adds predicate to rule
  p.push_back(in_pred);
}

string Rule::toString(){//Returns rule as a string
  stringstream list;
  int pLength = p.size();
  list << p.at(0);
  for(int i = 1; i < pLength; i++){
    list << "," << p.at(i);
  }
  stringstream out;
  out << headP << " :- " << list.str() << ".";
  return out.str();
}
