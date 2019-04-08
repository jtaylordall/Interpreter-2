#include "myScanner.h"

using namespace std;

myScanner::myScanner(string in) //constructor, automatically runs scanner
{
  worked = false;
  file = in;
  doScan();
}

myScanner::myScanner(){
  worked = false;
}

char myScanner::lookAhead(int a, string fc) //looks one char ahead in the string
{
  return fc.at(a+1);
}

void myScanner::testprint() //prints v to terminal
{
  int sz = v.size();
  for (int i = 0; i < sz; i++)
  {
    Token access = v.at(i);
    string out = access.createToken();
    cout << out << "\n";
  }
  cout << "Total Tokens = "<< sz << "\n";
  return;
}

void myScanner::doScan() //scans the file for tokens
{
  ifstream f;
  f.open(file); //opens file
  stringstream buf;
  buf << f.rdbuf();
  f.close();
  string fileContents = buf.str(); //move contents of file into a string
  int line_no = 1;
  char here;

  int fSize = fileContents.length();
  for(int i = 0; i <= fSize; i++) //iterate through the string and scan for tokens
  {
    if(i == (fSize)) //EOF
    {
      Token teof(eof, "", line_no);
      v.push_back(teof);
    }
    else
    {
      here = fileContents.at(i);
      int type;
      string value (1,here);
      if (isspace(here)) //white space
      {
        if ((int)here == 10) //increment line counter if white space is new line
        {
          line_no++;
        }
      }
      else if (isdigit(here)) //digit
      {
        type = undefined; //if digit, is automatically undefined
        Token t1(type, value, line_no);
        v.push_back(t1);
      }
      else if (isalpha(here)) //schemes, facts, queries, ids
      {
        //Schemes
        if((here == 'S')
        && (lookAhead(i, fileContents) == 'c')
        && (lookAhead(i+1, fileContents) == 'h')
        && (lookAhead(i+2, fileContents) == 'e')
        && (lookAhead(i+3, fileContents) == 'm')
        && (lookAhead(i+4, fileContents) == 'e')
        && (lookAhead(i+5, fileContents) == 's')
        && (!isalpha(lookAhead(i+6, fileContents))))
        {
          type = schemes;
          Token t2(type, "Schemes", line_no);
          v.push_back(t2);
          i = i + 6;
        }
        //Facts
        else if((here == 'F')
        && (lookAhead(i, fileContents) == 'a')
        && (lookAhead(i+1, fileContents) == 'c')
        && (lookAhead(i+2, fileContents) == 't')
        && (lookAhead(i+3, fileContents) == 's')
        && (!isalpha(lookAhead(i+4, fileContents))))
        {
          type = facts;
          Token t3(type, "Facts", line_no);
          v.push_back(t3);
          i = i + 4;
        }
        //Rules
        else if((here == 'R')
        && (lookAhead(i, fileContents) == 'u')
        && (lookAhead(i+1, fileContents) == 'l')
        && (lookAhead(i+2, fileContents) == 'e')
        && (lookAhead(i+3, fileContents) == 's')
        && (!isalpha(lookAhead(i+4, fileContents))))
        {
          type = rules;
          Token t3(type, "Rules", line_no);
          v.push_back(t3);
          i = i + 4;
        }
        //Queries
        else if((here == 'Q')
        && (lookAhead(i, fileContents) == 'u')
        && (lookAhead(i+1, fileContents) == 'e')
        && (lookAhead(i+2, fileContents) == 'r')
        && (lookAhead(i+3, fileContents) == 'i')
        && (lookAhead(i+4, fileContents) == 'e')
        && (lookAhead(i+5, fileContents) == 's')
        && (!isalpha(lookAhead(i+6, fileContents))))
        {
          type = queries;
          Token t4(type, "Queries", line_no);
          v.push_back(t4);
          i = i + 6;
        }
        //IDs
        else
        {
          stringstream str_id;
          char r = here;
          str_id << r;
          int g = i;
          g++;
          type = id;
          int temp_line = line_no;
          while((isdigit(r)) || (isalpha(r)))
          {
            r = fileContents.at(g);
            if ((int)r == 32) //space
            {
              g++;
              break;
            }
            else if ((int)r == 10) //new line
            {
              g++;
              line_no++;
              break;
            }
            else if ((!isdigit(r)) && (!isalpha(r)))
            {
              break;
            }
            str_id << r;
            g++;
          }
          value = str_id.str();
          Token tid(type, value, temp_line);
          v.push_back(tid);
          g--;
          i = g;
        }
      }
      else if((int)here == 39) //string literal, 39 = '
      {
        int line_start_str = line_no;
        stringstream str_lit;
        char st = fileContents.at(i);
        str_lit << st; //store opening apostrophe
        int z = i;
        type = string_;
        z++;
        st = fileContents.at(z);
        while(z != (fSize)) //stay in loop until hits ascii 39 = '
        {
          st = fileContents.at(z);
          if((int)st == 10)
          {
            line_no++;
          }
          str_lit << st;
          if(((int)st == 39) && ((int)lookAhead(z, fileContents) == 39))
          {
            str_lit << "'";
            z++;
          }
          else if(((int)st == 39) && ((int)lookAhead(z, fileContents) != 39))
          {
            z++;
            break;
          }
          z++;
        }
        z--;
        if (z == (fSize - 1))
        {
          type = undefined;
        }
        //}
        string s = str_lit.str();
        Token tstr(type, s, line_start_str);
        v.push_back(tstr);
        i = z;
      }
      else if(((int)here == 35) && ((int)lookAhead(i, fileContents) != 124)) //single-line comments
      {
        stringstream single_com;
        char u = fileContents.at(i);
        single_com << u;
        type = comment;
        int x = i;
        x++;
        while(x != fSize)
        {
          u = fileContents.at(x);
          if ((int)u == 10)
          {
            break;
          }
          else
          {
            single_com << u;
          }
          x++;
        }
        x--;
        string single_com_str = single_com.str();
        Token tscom(type, single_com_str, line_no);
        v.push_back(tscom);
        i = x;
      }
      else if(((int)here == 35) && ((int)lookAhead(i, fileContents) == 124)) //comments, 35 = #, 124 = |
      {
        int line_start_com = line_no;
        type = comment;

        stringstream a_com;
        char c = fileContents.at(i);
        a_com << c; //store opening #

        int y = i;
        y++;
        c = fileContents.at(y);
        a_com << c; //store opening |

        if((y + 1) != (fSize))
        {
          y++;
          while(y != (fSize))
          {
            c = fileContents.at(y);
            if((int)c == 10)
            {
              line_no++;
            }
            if(((int)c == 124) && ((int)lookAhead(y, fileContents) == 35))
            {
              a_com << c;
              y++;
              c = fileContents.at(y);
              a_com << c;
              y++;
              break;
            }
            else
            {
              a_com << c;
              y++;
            }
          }
        }
        if (y == (fSize))
        {
          type = undefined;
        }
        y--;
        string c_product = a_com.str();
        Token tcom(type, c_product, line_start_com);
        v.push_back(tcom);
        i = y;
      }
      else //punctuation
      {
        if(here == ',')
        {
          type = comma;
        }
        else if (here == '.')
        {
          type = period;
        }
        else if (here == '?')
        {
          type = q_mark;
        }
        else if (here == ':')
        {
          if (lookAhead(i, fileContents) == '-')
          {
            type = colon_dash;
            value = ":-";
            i++;
          }
          else
          {
            type = colon;
          }
        }
        else if (here == '*')
        {
          type = multiply;
        }
        else if (here == '+')
        {
          type = add;
        }
        else if (here == '(')
        {
          type = left_paren;
        }
        else if (here == ')')
        {
          type = right_paren;
        }
        else
        {
          type = undefined;
        }
        Token tpun(type, value, line_no);
        v.push_back(tpun);
      }
    }
  }
  //testprint(); //not needed for past lab 1
  worked = true;
  return;
}

vector<Token> myScanner::getTokens() //returns vector, for handing off to parser
{
  return v;
}

string myScanner::getFile(){
  ifstream f;
  f.open(file); //opens file
  stringstream buf;
  buf << f.rdbuf();
  f.close();
  string fileContents = buf.str();
  return fileContents;
}

bool myScanner::success(){
  return worked;
}
