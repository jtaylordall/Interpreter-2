#include "Predicate.h"

//Constructors
Predicate::Predicate(){} //Unparameterized Constructor

Predicate::Predicate(string in_id){//Parameterized Constructor
  p_id = in_id;
}


//addParam Functions
void Predicate::addParam(string p){//Adds new parameter to predicate
  parlist.push_back(p);
  return;
}

void Predicate::addParam_D(string p){//Adds new strings to Domain predicate if does not exist already
  int v_size = parlist.size();
  bool exists = false;
  for(int i = 0; i < v_size; i++){
    string here = parlist.at(i);
    if(p == here){
      exists = true;
    }
  }
  if(exists == false){
    parlist.push_back(p);
  }
  return;
}

void Predicate::sort_D(){//Sorts parameters alphabetically
  set<string> reorder;

  while(parlist.size() != 0){
    reorder.insert(parlist.at(parlist.size() - 1));
    parlist.pop_back();
  }

  for(set<string>::iterator it = reorder.begin(); it != reorder.end(); it++){
    string here = *it;
    parlist.push_back(here);
  }

  return;
}


//toString Functions
string Predicate::toString(){//Returns basic predicate as string
  stringstream list;
  int parlistLength = parlist.size();
  if(parlistLength > 0){
    list << parlist.at(0);
    for(int i = 1; i < parlistLength; i++){
      if(parlist.at(i) == "+" || parlist.at(i) == "*" || parlist.at(i-1) == "+" || parlist.at(i-1) == "*"){
        list << parlist.at(i);
      }
      else{
        list << "," << parlist.at(i);
      }
    }
  }
  string out = p_id + "(" + list.str() + ")";
  return out;
}

string Predicate::toString_exp(){//Returns basic predicate as string
  stringstream list;
  int parlistLength = parlist.size();
  if(parlistLength > 0){
    list << parlist.at(0);
    for(int i = 1; i < parlistLength; i++){
      if(parlist.at(i) == "+" || parlist.at(i) == "*" || parlist.at(i-1) == "+" || parlist.at(i-1) == "*"){
        list << parlist.at(i);
      }
      else{
        list << "," << parlist.at(i);
      }
    }
  }
  string out = p_id + list.str() + ")";
  return out;
}

string Predicate::toString_Q(){//Reurns query predicate as string w/ q_mark
  stringstream list;
  int parlistLength = parlist.size();
  if(parlistLength > 0){
    list << parlist.at(0);
    for(int i = 1; i < parlistLength; i++){
      if(parlist.at(i) == "+" || parlist.at(i) == "*" || parlist.at(i-1) == "+" || parlist.at(i-1) == "*"){
        list << parlist.at(i);
      }
      else{
        list << "," << parlist.at(i);
      }
    }
  }
  string out = p_id + "(" + list.str() + ")?";
  return out;
}

string Predicate::toString_High(){//Returns higher predicate as a string
  stringstream list;
  int parlistLength = parlist.size();
  if(parlistLength > 0){
    list << "  " << parlist.at(0) << "\n";
    for(int i = 1; i < parlistLength; i++){
      list << "  " << parlist.at(i) << "\n";
    }
  }
  stringstream out;
  out << p_id << "(" << parlistLength << "):\n" << list.str();
  return out.str();
}
