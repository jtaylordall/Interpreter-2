#include <iostream>
#include <vector>
#include <cstdlib>
#include "myScanner.h"
#include "Token.h"
#include "myParser.h"
#include "myInterpreter.h"

using namespace std;

int main(int argc, char *argv[]) //pass in arguments (file name) from command line
{
  myScanner s(argv[1]); //create scanner object, opens file and scans automatically
  if(s.success()){ //only parses if Scanner succeeds
    myParser p(s.getTokens()); //creates parser object, passes in vector of Tokens from s
    if(p.success()){ //only interprets if Parser succeeds
      vector<Token> tt = p.getTokens();
      myInterpreter i(tt); //creates interpreter object, passes in vector of Tokens from p (with comments removed)
    }
  }
  return 0;
}
