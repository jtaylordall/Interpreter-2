#pragma once

#include <iostream>
#include <cstdlib>
#include <vector>
#include <string>
#include <sstream>
#include <set>
#include "Parameter.h"

using namespace std;

class Predicate{
private:
  string p_id; //Predicate id name
  vector<string> parlist; //Vector list of parameters

public:
  //Constructors
  Predicate(string in_id);
  Predicate();

  //addParam Functions
  void addParam(string p);
  void addParam_D(string p);
  void sort_D();

  //toString Functions
  string toString();
  string toString_exp();
  string toString_Q();
  string toString_High();
};
