#include "Database.h"

//Constructor
Database::Database(){}


//Member Functions
void Database::addRelation(Relation &r){//adds Relation with linked name to Database
  db.insert(pair<string, Relation>(r.getName(), r));
  return;
}

void Database::print(){//couts Database by relations
  for(map<string, Relation>::iterator it = db.begin(); it !=db.end(); it++){
    it->second.print(); //prints relation in non-interpreted format
  }
  return;
}

map<string, Relation>::iterator Database::find(string in){//Returns iterator of relation with desired name
  return db.find(in);
}

int Database::getSize(){
  return db.size();
}

map<string, Relation> Database::getDB(){
  return db;
}
