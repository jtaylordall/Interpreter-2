#include "Parameter.h"

Parameter::Parameter(string in_value){//Parameterized Constructor
  value = in_value;
}

Parameter::Parameter(){//Unparameterized Constructor
  value = "";
}

string Parameter::par_toString(){//Returns parameter as string
  return value;
}
