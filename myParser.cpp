#include "myParser.h"

using namespace std;

//Constructor
myParser::myParser(vector<Token> in) {//Automatically initiates parsing when myParser object is initialized
  v = in;
  remove_comments(); //Removes comment tokens from vector v
  i = 0;
  v2 = v;
  tok = v.at(i);
  dom = Predicate("Domain");
  worked = false;
  catchErrors();
}


//Parameter Grammars
void myParser::op(Predicate *pred){//Grammar for operators
  int type = tok.getTypeint();
  if(type == _add){
    Parameter param(tok.getValue());
    match(_add);
    //    cout << param.par_toString() << "\n";
    (*pred).addParam(param.par_toString());
  }
  else if(type == _multiply){
    Parameter param(tok.getValue());
    match(_multiply);
    (*pred).addParam(param.par_toString());
  }
  else{
    error();
  }
  return;
}

void myParser::expression(Predicate *pred){//Grammar for expressions
  Predicate localPred(tok.getValue());
  match(_left_paren);
  parameter(&localPred);
  op(&localPred);
  parameter(&localPred);
  match(_right_paren);
  (*pred).addParam(localPred.toString_exp());
  return;
}

void myParser::parameter(Predicate *pred){//Grammar for parameters of basic and higher predicates
  int type = tok.getTypeint();
  if(type == _string){
    Parameter param(tok.getValue());
    match(_string);
    (*pred).addParam(param.par_toString());
  }
  else if(type == _id){
    Parameter param(tok.getValue());
    match(_id);
    (*pred).addParam(param.par_toString());
  }
  else{
    expression(pred);
  }
  return;
}


//Parameter Lists
void myParser::idList(Predicate *pred){
  if(tok.getTypeint() != _right_paren){
    match(_comma);
    Parameter param(tok.getValue());
    (*pred).addParam(param.par_toString());
    match(_id);
    idList(pred);
  }
  else {
    return;
  }
}

void myParser::stringList(Predicate *pred){
  if(tok.getTypeint() != _right_paren){
    match(_comma);
    Parameter param(tok.getValue());
    (*pred).addParam(param.par_toString());
    add_domain(tok.getValue());//Adds strings to Domain
    match(_string);
    stringList(pred);
  }
  else {
    return;
  }
}

void myParser::parameterList(Predicate *pred){
  if(tok.getTypeint() != _right_paren){
    match(_comma);
    parameter(pred);
    parameterList(pred);
  }
  else {
    return;
  }
}


//Predicate Grammars
Predicate myParser::headPredicate(){//Builds head predicate
  Predicate localPred(tok.getValue());
  match(_id);
  match(_left_paren);
  localPred.addParam(tok.getValue());
  match(_id);
  idList(&localPred);
  match(_right_paren);
  return localPred;
}

void myParser::predicate(Predicate *pred){//Builds basic predicate
  Predicate localPred(tok.getValue());
  match(_id);
  match(_left_paren);
  parameter(&localPred);
  parameterList(&localPred);
  match(_right_paren);
  (*pred).addParam(localPred.toString());
  return;
}

Predicate myParser::predicate2(){//Returns a predicate
  Predicate localPred(tok.getValue());
  match(_id);
  match(_left_paren);
  parameter(&localPred);
  parameterList(&localPred);
  match(_right_paren);
  return localPred;
}

void myParser::predicate_Q(Predicate *pred){//Builds predicate for query, basically adds q_mark on end
  Predicate localPred(tok.getValue());
  match(_id);
  match(_left_paren);
  parameter(&localPred);
  parameterList(&localPred);
  match(_right_paren);
  (*pred).addParam(localPred.toString_Q());
  return;
}

void myParser::predicate_VoP(vector<Predicate> *VoP){//Adds predicates to vector v
  Predicate localPred(tok.getValue());
  match(_id);
  match(_left_paren);
  parameter(&localPred);
  parameterList(&localPred);
  match(_right_paren);
  (*VoP).push_back(localPred);
  return;
}


//Predicate Lists
void myParser::predicateList(Predicate *pred){//Normal predicate list
  if(tok.getTypeint() == _period){
    return;
  }
  else{
    match(_comma);
    predicate(pred);
    predicateList(pred);
  }
}

void myParser::predicateList_VoP(vector<Predicate> *VoP){//Predicate list for rules
  if(tok.getTypeint() == _period){
    return;
  }
  else{
    match(_comma);
    predicate_VoP(VoP);
    predicateList_VoP(VoP);
  }
}


//Higher Predicate Grammars
void myParser::scheme(Predicate *pred){
  Predicate localPred(tok.getValue());
  match(_id);
  match(_left_paren);
  Parameter param(tok.getValue());
  localPred.addParam(param.par_toString());
  match(_id);
  idList(&localPred);
  match(_right_paren);
  (*pred).addParam(localPred.toString());
  return;
}

void myParser::fact(Predicate *pred){
  Predicate localPred(tok.getValue());
  match(_id);
  match(_left_paren);
  Parameter param(tok.getValue());
  localPred.addParam(param.par_toString());
  add_domain(tok.getValue());//Adds strings to Domain
  match(_string);
  stringList(&localPred);
  match(_right_paren);
  match(_period);
  (*pred).addParam(localPred.toString()+ ".");
  return;
}

void myParser::rule(Predicate *pred){
  Predicate localHeadPred;
  localHeadPred = headPredicate(); //reassigns localHeadPred
  Rule localRule(localHeadPred.toString()); //adds localHeadPred to rule

  match(_colon_dash);

  vector<Predicate> VoP; //vector for storing predicates to localRule
  VoP.push_back(predicate2());
  predicateList_VoP(&VoP);

  match(_period);

  int VoP_size = VoP.size();
  for(int j = 0; j < VoP_size; j++){//Adds VoP elements as predicates to localRule
    Predicate temp = VoP.at(j);
    localRule.addPred(temp.toString());
  }

  (*pred).addParam(localRule.toString());

  return;
}

void myParser::query(Predicate *pred){

  predicate_Q(pred);
  match(_q_mark);
  return;
}


//Higher Predicate Lists
void myParser::schemeList(Predicate *pred){
  if(tok.getTypeint() == _schemes || tok.getTypeint() == _id){
    scheme(pred);
    schemeList(pred);
  }
  else if(tok.getTypeint() == _facts){ //ends when gets to Facts token
    return;
  }
  else{
    error();
  }
}

void myParser::factList(Predicate *pred){
  if(tok.getTypeint() == _facts || tok.getTypeint() == _id){
    fact(pred);
    factList(pred);
  }
  else if(tok.getTypeint() == _rules){
    return;
  }
  else{
    error();
  }
}

void myParser::ruleList(Predicate *pred){
  if(tok.getTypeint() == _rules || tok.getTypeint() == _id){
    rule(pred);
    ruleList(pred);
  }
  else if(tok.getTypeint() == _queries){ //ends when gets to Queries token
    return;
  }
  else{
    error();
  }
}

void myParser::queryList(Predicate *pred){
  if(tok.getTypeint() != _eof && tok.getTypeint() == _id){
    query(pred);
    queryList(pred);
  }
  else {
    return;
  }
}


//Primary Driving Functions
void myParser::remove_comments(){//Removes comment tokens from vector v
  int v_size = v.size();
  Token here;
  for(int a = 0; a < v_size; a++){
    here = v.at(a);
    if(here.getTypeint() == _comment){
      //cout << "remove " << here.getType() << ": "<< here.getValue() << "\n"; //for testing if comments are actuall removed
      v.erase(v.begin() + a);
      a--;
      v_size--;
    }
    else if(here.getTypeint() == _undefined){
      error();
    }
  }
  return;
}

void myParser::catchErrors(){//if catches errors, prints failure. else prints success

  DatalogProgram dat;
  try{

    dat = datalogProgram();

  }
  catch (Token t){
    cout << "Failure!\n  "<< t.createToken() << "\n";
    return;
  }
  //dat.output(); //removed for interpreter stage
  worked = true;
  return;
}

DatalogProgram myParser::datalogProgram(){//Runs through datalogProgram and catches any errors thrown

  DatalogProgram dat2;
  while(tok.getTypeint() != _eof){
    Predicate sch(tok.getValue());
    //  Predicate& rsch = sch;
    match(_schemes);
    match(_colon);
    scheme(&sch);
    schemeList(&sch);

    Predicate fac(tok.getValue());
    match(_facts);
    match(_colon);
    factList(&fac);

    Predicate rul(tok.getValue());
    match(_rules);
    match(_colon);
    ruleList(&rul);

    Predicate que(tok.getValue());
    match(_queries);
    match(_colon);
    query(&que);
    queryList(&que);

    if(tok.getTypeint() != _eof){
      error();
    }

    dom.sort_D(); //Sorts Domain alphabetically

    DatalogProgram dat(sch.toString_High(), fac.toString_High(), rul.toString_High(), que.toString_High(), dom.toString_High());
    dat2 = dat;
    return dat;
  }
  return dat2;
}


//Supporting Functions
void myParser::match(int type){//Checks to see if Token type is correct, else calls error()
  if (type == tok.getTypeint()){
    i++;
    tok = v.at(i);
  }
  else{
    error();
  }
  return;
}

void myParser::add_domain(string in){//Adds strings to domain
  dom.addParam_D(in);
  return;
}

void myParser::error(){//throws an error and increments i
  throw tok;
  i++;
}

bool myParser::success(){
  return worked;
}

vector<Token> myParser::getTokens(){
  return v2;
}
