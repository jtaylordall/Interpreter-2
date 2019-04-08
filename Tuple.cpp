#include "Tuple.h"

//Constructors
Tuple::Tuple(){}

Tuple::Tuple(vector<string> v_in){
  v = v_in;
/*  if(v.size() > 0){
    v0 = v.at(0);
  }*/
}


//Member Functions
string Tuple::toString(){//Returns Tuple as a string
  stringstream ss;
  int vSize = v.size();
  ss << "(";
  for(int a = 0; a < vSize; a++){
    ss << v.at(a);
    if(a != vSize - 1){
      ss << ",";
    }
  }
  ss << ")";
  return ss.str();
}

vector<string> Tuple::getTuple(){//Returns Tuple as a vector of strings
  return v;
}

int Tuple::getSize(){//Returns size of v
  return v.size();
}
