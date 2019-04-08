#pragma once

#include <iostream>
#include <cstdlib>
#include <vector>
#include <string>
#include <sstream>

using namespace std;

class Scheme{
private:
  vector<string> att; //vector containing Scheme attributes as strings

public:
  //Constructors
  Scheme();
  Scheme(vector<string> att_in);

  //Member Functions
  vector<string> getScheme(); //Returns Scheme as a vector
  string toString(); //Returns Scheme as a string
};
