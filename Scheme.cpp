#include "Scheme.h"

//Constructors
Scheme::Scheme(){}

Scheme::Scheme(vector<string> att_in){
  att = att_in;
}


//Member Functions
vector<string> Scheme::getScheme(){//Returns Scheme as a vector
  return att;
}

string Scheme::toString(){//Returns Scheme as a string
  stringstream ss;
  int attSize = att.size();
  ss << "(";
  for(int a = 0; a < attSize; a++){
    ss << att.at(a);
    if(a != attSize - 1){
      ss << ",";
    }
  }
  ss << ")";
  return ss.str();
}
