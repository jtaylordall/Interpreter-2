#include "Token.h"

string Token::getType() //converts type from int (enum) into string
{
  switch(type)
  {
    case comma: new_type = "COMMA";
    break;
    case period: new_type = "PERIOD";
    break;
    case q_mark: new_type = "Q_MARK";
    break;
    case left_paren: new_type = "LEFT_PAREN";
    break;
    case right_paren: new_type = "RIGHT_PAREN";
    break;
    case colon: new_type = "COLON";
    break;
    case colon_dash: new_type = "COLON_DASH";
    break;
    case multiply: new_type = "MULTIPLY";
    break;
    case add: new_type = "ADD";
    break;
    case schemes: new_type = "SCHEMES";
    break;
    case facts: new_type = "FACTS";
    break;
    case rules: new_type = "RULES";
    break;
    case queries: new_type = "QUERIES";
    break;
    case id: new_type = "ID";
    break;
    case string_: new_type = "STRING";
    break;
    case comment: new_type = "COMMENT";
    break;
    case eof: new_type = "EOF";
    break;
    default: new_type = "UNDEFINED";
  }
  return new_type;
}

int Token::getTypeint()
{
  return type;
}

Token::Token() //unparameterized constructor
{
  line = 999;
  type = 999;
  value = "";
  new_type = "";
}

Token::Token(int in_type, string in_value, int in_line) //parameterized constructor
{
  line = in_line;
  type = in_type;
  value = in_value;
  new_type = getType();
}

Token::~Token() {} //destructor

string Token::createToken() //returns token as a string
{
  stringstream forge;
  string newforge;
  forge << "("<< new_type << ",\""<< value << "\","<< line << ")";
  newforge = forge.str();
  return newforge;
}

string Token::getValue(){
  return value;
}

int Token::getLineNo(){
  return line;
}
