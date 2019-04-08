#pragma once

#include <iostream>
#include <cstdlib>
#include <vector>
#include <string>
#include <sstream>

using namespace std;

class Parameter{
private:
  string value;

public:
  Parameter(string in_value);
  Parameter();
  string par_toString();
};
