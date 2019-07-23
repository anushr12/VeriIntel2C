#include <iostream>
#include <new>
#include <stdio.h>
#include <string.h>
//#include "analysis_parse.h"


typedef struct declare_data{

  int bit_width;
  bool array; //VeriVariable->IsArray()
  bool next_operator_out; //for checking if there is more than one operator attached
  bool next_selector_out; //for checking if there is more than one signal selector attached
  bool next_comparator_out;
  //type_d data_type; // VeriVariable->IsType() , mention if it is input type
  const char *name;
  int dimensions;
  unsigned unary_operator;
  /*
  struct operate_op_struct *operator_in;
  struct operate_op_struct *operator_out;
  struct signal_select_struct *signal_selector_out; //pointing to the signal selector
  struct equal_to_struct *equal_op_out; //pointing to assignto equal operator
  struct Compare_op_struct *comparator_out; //pointing to comparator
  struct trans_struct *transition_out;
  struct place_struct *place_ptr;
  struct DFG_struct *dfgnode_out;
  */
  struct trans_struct *transition_out;
  struct declare_data *next_n;
  struct declare_data *prev_n;
  
}DeclareData;



struct Path_list
{
public:
 // Path_list( const std::string& name )
//   :m_name( name )
 // {};
 
 // const std::string m_name;
};

typedef struct Place_struct : public Path_list
{
  public:
  DeclareData *first_place_input; //control inputs to the placenode 
DeclareData *state_place_input; //control state inputs to the place
  struct trans_struct *transition_n;
  /*
  C1( const int var )
    :P( "C1" )
    ,m_var( var )
  {};
 
  const int m_var;
  */
}Place_node;

typedef struct trans_struct : public Path_list
{
  public:
  DeclareData *output_var; 
  char *name;
  /*
  C2( const int var )
    :P( "C2" )
    ,m_var( var )
  {};
 
  int m_var;
  */
}trans_node;


void foo(trans_node** ,trans_node *);

///////////////////////////


int main (int argc, char *argv[])
{
  //
	char *n;
    //array pointer
    
    Path_list* p[10];
    trans_node *t[10];
    trans_node *tr;
    
    tr = new trans_node;
    tr->name = "anu";
    foo(t,tr);
    trans_node *t1 = new trans_node;
    
    p[1] = t1;
    n = (static_cast< trans_node* >(p[1]))->name;
    //p[1]->name = 'a';
    //first one
   // p[1] = new C1( 1 );
   // p[2] = new C2( 2 );

	std::cout<< "name:" << t[1]->name << std::endl;
  //  std::cout<< "p" << p << std::endl;
   // std::cout<< "p[1]->m_name :" << p[1]->m_name << std::endl;
   // std::cout<< "p[2]->m_name :" << p[2]->m_name << std::endl;
    
  // std::cout<< (static_cast< C2* >(p[1]))->m_var << std::endl;
  //  std::cout<< (static_cast< C2* >(p[2]))->m_var << std::endl;
    
    // std::cout<< "dynamic_cast< C1 >(p[1])->m_var :" << dynamic_cast< C1 >(p[1])->m_var << std::endl;
    // std::cout<< "dynamic_cast< C2 >(p[1])->m_var :" << dynamic_cast< C1 >(p[1])->m_var << std::endl;
    
  

}




void foo(trans_node** t_temp,trans_node *tmp){

//int i =0;

t_temp[0] = tmp;
t_temp[1] = tmp;
}







