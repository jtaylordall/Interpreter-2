#include "Relation.h"

//Constructors
Relation::Relation(){}

Relation::Relation(string name_in, Scheme &sch_in){
  name = name_in;
  sch = sch_in;
}

Relation::Relation(string name_in, Scheme &sch_in, int order_in){
  name = name_in;
  sch = sch_in;
  order = order_in;
}

Relation::Relation(string name_in, Scheme &sch_in, set<Tuple> &tup_in){
  name = name_in;
  sch = sch_in;
  tup = tup_in;
}


//Push Functions
void Relation::changename(string in){//changes the name(data member) of the Relation
  name = in;
  return;
}

void Relation::addTuple(Tuple &t){//Adds new Tuple to relation
  tup.insert(t);
  return;
}

void Relation::addQuery(Tuple &q){//adds query for relations to be outputed
  que = q;
  return;
}

void Relation::addScheme2(vector<string> in){
  Scheme s(in);
  sch2 = s;
  return;
}

void Relation::addOrder(int order_in){
  order = order_in;
  return;
}


//Pull Functions
string Relation::getName(){//Returns name of Relation
  return name;
}

int Relation::getSize(){//returns number of tuples in the relation
  return tup.size();
}

vector<string> Relation::getQuery(){//returns contents of query
  return que.getTuple();
}

vector<string> Relation::getScheme(){
  return sch.getScheme();
}

vector<string> Relation::getScheme2(){
  return sch2.getScheme();
}

void Relation::print(){//prints out relation, unformatted
  cout << "Name: " << name << "\n";
  cout << "Scheme:" << sch.toString() << "\nTuples:\n";
  for (it = tup.begin(); it != tup.end(); ++it){ //interates through each tuple in the relation
    Tuple iter = *it;
    cout << "  " << iter.toString() << "\n"; //prints out each tuple
  }
  cout << "\n";
  return;
}

void Relation::print_cerr(){//prints out relation, unformatted
  cerr << "Name: " << name << "\n";
  cerr << "Scheme:" << sch.toString() << "\nTuples:\n";
  for (it = tup.begin(); it != tup.end(); ++it){ //interates through each tuple in the relation
    Tuple iter = *it;
    cerr << "  " << iter.toString() << "\n"; //prints out each tuple
  }
  cerr << "\n";
  return;
}

void Relation::print_output_q(){//prints out relation, formatted for Interpreter
  cout << name << que.toString() << "? ";
  if(getSize() > 0){ //shows status of query assessment
    cout << "Yes(" << getSize() << ")\n";
  }
  else{
    cout << "No\n";
  }
  vector<string> s = sch.getScheme(); //store scheme (post-projection and rename)
  int sSize = s.size();
  for (it = tup.begin(); it != tup.end(); ++it){ //iterates through each tuple
    int counter = 0;
    for(int a = 0; a < sSize; a++){ //iterates through contents of scheme to get number of variables(post-duplicate-removal), stores it
      if((int)s.at(a).at(0) != 39){
        counter++;
      }
    }
    int counter2 = 0;
    for(int a = 0; a < sSize; a++){ //iterates through contents of scheme again
      if((int)s.at(a).at(0) != 39){ //if element from scheme is a variable, prints out variable and associated constant from tuple
        counter2++;
        if(counter2 == 1){ //if is first variable, adds indent of 2 spaces
          cout << "  ";
        }
        Tuple iter = *it;
        cout << s.at(a) << "=" << iter.getTuple().at(a);
        if(counter != counter2){ //if is last variable, prints newline
          cout << ", ";
        }
        else{ //otherwise prints comma and space
          cout << "\n";
        }
      }
    }
  }
  return;
}

void Relation::print_output_r(){
  vector<string> s = sch2.getScheme(); //store scheme (post-projection and rename)
  int sSize = s.size();
  for (it = tup.begin(); it != tup.end(); ++it){ //iterates through each tuple
    int counter = 0;
    for(int a = 0; a < sSize; a++){ //iterates through contents of scheme to get number of variables(post-duplicate-removal), stores it
      if((int)s.at(a).at(0) != 39){
        counter++;
      }
    }
    int counter2 = 0;
    for(int a = 0; a < sSize; a++){ //iterates through contents of scheme again
      if((int)s.at(a).at(0) != 39){ //if element from scheme is a variable, prints out variable and associated constant from tuple
        counter2++;
        if(counter2 == 1){ //if is first variable, adds indent of 2 spaces
          cout << "  ";
        }
        Tuple iter = *it;
        cout << s.at(a) << "=" << iter.getTuple().at(a);
        if(counter == counter2){ //if is last variable, prints newline
          cout << "\n";
        }
        else{ //otherwise prints comma and space
          cout << ", ";
        }
      }
    }
  }
  return;
}

set<Tuple> Relation::getTuples(){
  return tup;
}


//Relational Operations
Relation Relation::select_pv(int position, string value){//Finds tuples that have value at position, for assessing constants
  Relation r(name, sch); //creates empty new relation on standby
  for (it = tup.begin(); it != tup.end(); ++it){ //iterates through all tuples in the current relation
    Tuple iter = *it;
    vector<string> test;
    test = iter.getTuple(); //stores contents of tuple in a vector
    if (test.at(position) == value){ //if element at position matches value in question, adds tuple to the new relation
      Tuple t(test);
      r.addTuple(t);
    }
  }
  return r; //returns new relation with selected tuples
}

Relation Relation::select_pp(vector<int> positions){//Finds tuples that have same value at specified positions, for assessing variables
  vector<string> test;
  int posSize = positions.size();
  Relation r(name, sch); //creates empty new relation of standby
  for (it = tup.begin(); it != tup.end(); ++it){ //iterate through all tuples in current relation
    string old = "";
    bool same = true;
    Tuple iter = *it;
    for(int a = 0; a < posSize; a++){ //iterate through positions
      test = iter.getTuple();
      string news = test.at(positions.at(a)); //check if elements at desired positions are all the same
      if(news != old && old != ""){ //if finds one instance of not matching previous element(which should be the same), discards current tuple
        same = false;
        break;
      }
      old = news;
    }
    if(same){
      Tuple t(test);
      r.addTuple(t); //if all elements are the same for indicated positions, add tuple to the relation
    }
  }
  return r; //return relation of valid tuples
}

Relation Relation::project(vector<int> positions){//projects relation according to the positions vector

  if(positions.size() == 0 || getSize() == 0){ //only proceeds if positions vector size is bigger than zero
    Relation rempty(name, sch);
    return rempty; //otherwise returns empty vector
  }

  //Step 1: Reorganize relation to be grouped as columns instead of rows
  it = tup.begin();
  Tuple iter = *it;
  int sizeTup = iter.getSize();

  vector<Tuple> listofcolumns;  //vector for storing contents of columns, each column is a tuple
  for(int i = 0; i < sizeTup; i++)//iterates through the positions of a generic tuple the size of the current relation's tuples
  {
    vector<string> columncontents;
    for(it = tup.begin(); it != tup.end(); ++it){ //iterates through each of the tuples in the current relations
      iter = *it;
      vector<string> row = iter.getTuple();
      string temp = row.at(i);
      columncontents.push_back(temp); //stores the element at the current position in the column vector
    }
    Tuple column(columncontents); //stores the column vector as a tuple in the list of columns
    listofcolumns.push_back(column);
  }

  //Step 2: Select specified columns and reorder according to positions vector
  vector<Tuple> listofcolumns2;
  int posSize = positions.size();

  for(int j = 0; j < posSize; j++){//iterates through positions vector
    int columnget = positions.at(j); //finds column at corresponding position
    Tuple t(listofcolumns.at(columnget));
    listofcolumns2.push_back(t); //adds column as tuple to new list of columns vector
  }

  //Step 3: Reorganize relation to be grouped into rows again
  int loc2Size = listofcolumns2.size();
  set<Tuple> newtup; //create empty new set of tuples
  int cbdSize = listofcolumns2.at(0).getTuple().size();

  for(int l = 0; l < cbdSize; l++){ //iterate through the column vector
    vector<string> rowbuild;
    for(int k = 0; k < loc2Size; k++){ //iterate through generic tuple of appropriate length
      rowbuild.push_back(listofcolumns2.at(k).getTuple().at(l)); //add elements on same row into same vector
    }
    Tuple newt(rowbuild);
    newtup.insert(newt); //store row vector as a tuple and add it to new set of tuples
  }
  Scheme ss = project_scheme(positions);
  Relation r(name, ss, newtup); //create new relation with projected scheme and projected set of tuples
  return r; //return new projected relation
}

Scheme Relation::project_scheme(vector<int> &positions){//rearranges scheme according to positions vector, supports project()
  vector<string> currentScheme = sch.getScheme();
  vector<string> newScheme; //create new vector for scheme on standby
  int posSize = positions.size();
  for(int i = 0; i < posSize; i++){ //iterate through positions vector
    int attget = positions.at(i); //find scheme attribute corresponding to specified position
    newScheme.push_back(currentScheme.at(attget)); //store scheme attribute in new scheme vector
  }
  Scheme s(newScheme); //create new projected scheme and return it
  return s;
}

Relation Relation::rename(Scheme &in){//replaces the scheme with inputed one
  Relation r(name, in, tup); //creates new relation with new scheme, but old name and set of tuples
  return r;
}

Relation Relation::join(Relation &in){

  //vector<string> in_sch = in.getScheme();
  int in_sch_size = in.getScheme().size();
  //vector<string> cur_sch = getScheme();
  int cur_sch_size = getScheme().size();

  //find matching columns by positions
  vector<vector<int>> columns;
  for(int a = 0; a < cur_sch_size; a++){
    for(int b = 0; b < in_sch_size; b++){
      if(getScheme().at(a) == in.getScheme().at(b)){
        vector<int> vec;
        vec.push_back(a);
        vec.push_back(b);
        columns.push_back(vec);  // {(in, cur), (in, cur), ...}
      }
    }
  }
  //combine schemes here
  vector<string> sch_dup = combineWithDuplicates(getScheme(), in.getScheme());
  map<string, vector<int>> linked = checkSameness(sch_dup); //find any duplicates variables or constants in query
  Scheme out_s = combineSchemes(getScheme(), in.getScheme());
  set<Tuple> in_tup = in.getTuples();
  set<Tuple>::iterator it_in;
  Relation out;
  out = out.rename(out_s);
  int columnsSize = columns.size();
  Scheme out_s_t(sch_dup);
  if(linked.size() != sch_dup.size()){
    if(sch_dup.size() > out_s.getScheme().size()){ // if has duplicates
      //find joinable tuples and created new joined tuple
      for(it_in = in_tup.begin(); it_in != in_tup.end(); it_in++){ //iterate through in_tup
        Tuple t_in = *it_in;
        vector<string> v_in = t_in.getTuple();
        for(it = tup.begin(); it != tup.end(); it++){ //iterate through tup
          Tuple t_cur = *it;
          vector<string> v_cur = t_cur.getTuple();
          for(int a = 0; a < columnsSize; a++){ //see if any tuples qualify to be joined
            if(v_cur.at(columns.at(a).at(0)) == v_in.at(columns.at(a).at(1))){
              Tuple joined_tuple_t(combineWithDuplicates(v_cur, v_in));
              out.addTuple(joined_tuple_t);
            }
          }
        }
      }

      for(map<string, vector<int>>::iterator mit = linked.begin(); mit != linked.end(); mit++){ //performs selects on variables
        out = out.select_pp(mit->second); //performs select based on position vector
      }
      out = out.rename(out_s_t);
      vector<int> vp = removeDuplicates_pos(sch_dup);
      out = out.project(vp);
    }
    else{
      for(it_in = in_tup.begin(); it_in != in_tup.end(); it_in++){ //iterate through in_tup
        Tuple t_in = *it_in;
        vector<string> v_in = t_in.getTuple();
        for(it = tup.begin(); it != tup.end(); it++){ //iterate through tup
          Tuple t_cur = *it;
          vector<string> v_cur = t_cur.getTuple();
          for(int a = 0; a < columnsSize; a++){ //see if any tuples qualify to be joined
            if(v_in.at(columns.at(a).at(0)) == v_cur.at(columns.at(a).at(1))){
              Tuple joined_tuple_t = combineTuples(v_cur, v_in);
              out.addTuple(joined_tuple_t);
            }
          }
        }
      }
    }
  }
  else{
    out = cartesianProduct(in);
    out = out.rename(out_s_t);
  }
  return out;
}

Scheme Relation::combineSchemes(vector<string> v1, vector<string> v2){
  vector<string> out = v1;
  int v1Size = v1.size();
  int v2Size = v2.size();
  set<string> v1set;
  for(int a = 0; a < v1Size; a++){
    v1set.insert(v1.at(a));
  }
  for(int a = 0; a < v2Size; a++){
    if(v1set.count(v2.at(a)) == 0){
      out.push_back(v2.at(a));
    }
  }
  Scheme s(out);
  return s;
}

vector<string> Relation::combineWithDuplicates(vector<string> v1, vector<string> v2){
  vector<string> out;
  int v2Size = v2.size();
  out = v1;
  for(int a = 0; a < v2Size; a++){
    out.push_back(v2.at(a));
  }
  return out;
}

Tuple Relation::combineTuples(vector<string> &v1, vector<string> &v2){
  vector<string> out = v1;
  int v1Size = v1.size();
  int v2Size = v2.size();
  set<string> v1set;
  for(int a = 0; a < v1Size; a++){
    v1set.insert(v1.at(a));
  }
  for(int a = 0; a < v2Size; a++){
    if(v1set.count(v2.at(a)) == 0){
      out.push_back(v2.at(a));
    }
  }
  Tuple t(out);
  return t;
}

Relation Relation::unionize(Relation &in){
  set<Tuple> in_tup = in.getTuples();
  Relation u(name, sch);
  for(it = in_tup.begin(); it != in_tup.end(); it++){
    Tuple temp = *it;
    if(tup.count(temp) == 0){
      tup.insert(temp);
      u.addTuple(temp);
    }
  }
  return u;
}

map<string,vector<int>> Relation::checkSameness(vector<string> &t_vec){//evaluates common parameters in aquery, assists assessquery()
  map<string, vector<int>> m;
  int t_vecSize = t_vec.size();
  vector<int> positions;

  //put strings from t into a map
  for(int a = 0; a < t_vecSize; a++){
    m.insert(pair<string, vector<int>>(t_vec.at(a), positions));
  }

  //find positions of t strings and stores in its associated vector
  for(map<string, vector<int>>::iterator it = m.begin(); it != m.end(); it++)
  {
    for(int a = 0; a < t_vecSize; a++)
    { //iterates through tuple's vector
    if(it->first == t_vec.at(a))
    { //if the variable/constant matches the tuples value then stores position
      it->second.push_back(a);
    }
  }
}
return m; //returns map containing variables with a vector of their respective positions
}

vector<int> Relation::removeDuplicates_pos(vector<string> &in){//returns positions of vector without duplicates, assists projection stage in assessquery()
  set<string> out;
  vector<int> out_int;
  int inSize = in.size();
  for(int a = 0; a < inSize; a++){ //iterates through vector in
    if(out.count(in.at(a)) == 0){
      out.insert(in.at(a));
      out_int.push_back(a);
    }
  }
  return out_int; //returns vector of positions excluding duplicates
}

Relation Relation::cartesianProduct(Relation &in){
  Relation out;
  //set<Tuple> tup_in = in.getTuples();
  set<Tuple>::iterator it_in;
  for(it_in = in.getTuples().begin(); it_in != in.getTuples().end(); it_in++){
    Tuple t_in = *it_in;
    for(it = tup.begin(); it != tup.end(); it++){
      Tuple t = *it;
      Tuple o(combineWithDuplicates(t.getTuple(),t_in.getTuple()));
      out.addTuple(o);
    }
  }
  return out;
}
