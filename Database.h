#pragma once

#include <iostream>
#include <cstdlib>
#include <string>
#include <map>
#include "Relation.h"
#include "Tuple.h"
#include "Scheme.h"

using namespace std;

class Database{
private:
  map<string, Relation> db; //Map linking names to Relations

public:
  //Constructor
  Database();

  //Member Funtions
  void addRelation(Relation &r); //adds Relation with linked name to Database
  void print(); //couts Database by relations
  map<string, Relation>::iterator find(string in); //Returns iterator of relation with desired name
  int getSize();
  map<string, Relation> getDB();
};
