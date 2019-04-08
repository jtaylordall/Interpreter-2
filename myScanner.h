#pragma once

#include <iostream>
#include <fstream>
#include <cstdlib>
#include <string>
#include <vector>
#include <cctype>
#include "Token.h"

using namespace std;

// scans input string
class myScanner{
private:
  string file; //file name passed in from main
  vector<Token> v; //vector stores all the tokens made by doScan
  void testprint(); //prints v to terminal
  bool worked;

public:
  myScanner(string in); //constructor, automatically runs scanner
  myScanner();
  void doScan(); //scans the file for tokens
  vector<Token> getTokens(); //returns vector, for handing of to parser
  char lookAhead(int a, string fc); //looks one char ahead in the string
  string getFile();
  bool success();

  enum Tokentype
  {
    comma,
    period,
    q_mark,
    left_paren,
    right_paren,
    colon,
    colon_dash,
    multiply,
    add,
    schemes,
    facts,
    rules,
    queries,
    id,
    string_,
    comment,
    undefined,
    eof
  };
};
