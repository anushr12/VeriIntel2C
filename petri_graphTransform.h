

#ifndef PETRI_GRAPH_TRANSFORM_H
#define PETRI_GRAPH_TRANSFORM_H





#include "VeriTreeNode.h"
#include "Array.h"
#include "VeriModuleItem.h"
#include "VeriModule.h"     // Definition of a VeriModule and VeriPrimitive
#include "VeriId.h"         // Definitions of all identifier definition tree nodes
#include "VeriExpression.h" // Definitions of all verilog expression tree nodes
#include "VeriStatement.h"  // Definitions of all verilog statement tree nodes
#include "VeriMisc.h"       // Definitions of all extraneous verilog tree nodes (ie. range, path, strength, etc...)
#include "VeriConstVal.h"   // Definitions of parse-tree nodes representing constant values in Verilog.
#include "VeriScope.h"      // Symbol table of locally declared identifiers
#include "VeriLibrary.h"    // Definition of VeriLibrary

#include "analysis_parse.h"

using namespace std;

#ifdef VERIFIC_NAMESPACE
using namespace Verific ;
#endif

extern Graph_node *graph_first_node;
extern State_var *first_state;

/*structures to describe the entities of the graph*/

// Data Flow Graph node block
typedef struct DFG_struct{

//struct operation_struct *first_node;
DeclareData *output;
//PortList *input_list;
//PortList *output_list;
struct cond_struct *condition_op;// to this the list of the condition blocks are attached for a single caseblock of a single always node
struct equal_to_struct *assignment_graph; // to this the assign expressions are attached
struct operate_op_struct *operation_graph; // to this the basic operation node is attached

}DFG_block;
//conditional block ,also represents switch case 
typedef struct cond_struct{
bool switchcase;
struct relation_op_struct *compare_cond;
struct declare_data *if_cond_var; // if the condition is just a variable and not an expression
struct equal_to_struct *equal_cond; // to store the condition when condition variable equals a case value, then the assign expression is attached
struct equal_to_struct *assign_expr; // expr related to the condition extracted from the caseblock
struct cond_struct *next_cond;
struct cond_struct *prev_cond;

}Condition_block;

// need to attach list of inputs to the place block

//place block
typedef struct place_struct{
DeclareData *first_place_input; //control inputs to the placenode 
DeclareData *state_place_input; //control state inputs to the place
bool next_trans_node; // flag to check if there is more than one transition node attached to one place
struct trans_struct *first_trans_node;
struct place_struct *next_place; //for parallel places
bool token_active;

}Place_block;

//need to insert list of inputs to the transition node

//transition block
typedef struct trans_struct{

struct place_struct *own_place_ptr; //pointing to its own place node
struct place_struct *outgoing_external_place; //pointing to external outgoing place node
DFG_block *outgoing_external_dfg ; 
struct declare_data *output_var;  
bool traverse_node; //flag to indicate if this transition is to be
struct trans_struct *next_trans_node;
struct trans_struct *prev_trans_node;
DFG_block *data_node;

}Transition_block;

typedef struct equal_to_struct{

struct declare_data *lhs_value;
struct declare_data *rhs_value;

char opsymbol;
struct equal_to_struct *next_equal; //EDITED
struct equal_to_struct *prev_equal;
}Equal_to_op;

typedef struct Compare_op_struct{

struct declare_data *lhs_compare; //this is the left value of the equal condition if it exists lhs_compare=value_compare
struct declare_data *condition_value; // this is for representing ifcondition var 
FSM_struct *state_condition; //if the ifconditionvar is a state signal
 const char *value_compare; //value the lhsvalue is compared to
//Equal_to_op *assign_value; //this is the outgoing expr executed if lhs_value is equal to rhs_value
DeclareData *value_out; //this is the outgoing value if the conditional node has only then_var
char opsymbol;
struct Compare_op_struct *next_comparator;
}Compare_operator;

//structure for control signal generator
typedef struct signal_select_struct{
struct declare_data *in_signal_list;
DeclareData *state_in_signal; //if input signal is a state
struct declare_data *out_signal;

struct signal_select_struct *next_selector;
}Signal_selector;


typedef struct operate_op_struct{

struct declare_data *op1;
struct declare_data *op2;
struct operate_op_struct *op3;
FSM_struct *op_state;
char op_type;
struct declare_data *output_value;
struct operate_op_struct *next_oper;
struct operate_op_struct *prev_oper;
}Operate_op;

// for storing the path of nodes to print in the C source code
typedef struct path_struct{

Operate_node *opnode;
DeclareData *varnode;
Assign_var *assignnode;
Always_block *alnode;
ModuleInstantiate *modnode;
Ifthenelse_block *condnode;
Case_Statement *casenode;
/*
Operate_op *opnode;

Place_block *placenode;
Transition_block *trannode;
Equal_to_op *equalnode;
DFG_block *dfgnode;*/

}Path_node;


//function prototype declaration


int create_petri_graph(struct node_struct * , struct FSM_struct *); 

void Select_from_operator_list(Operate_op *,ModuleInstantiate *, unsigned);
void delete_ports_list(PortList*& );
void delete_data_list(Graph_node *,State_var *);
void delete_null_nodes(int);
void delete_null_always_list( Always_block *);
void delete_nodes(Graph_node *,Assign_var *&,Operate_node *&,Ifthenelse_block *&);


  void insert_in_condition_list( Condition_block *, DFG_block *); 
  void Insert_placeInput_list( Place_block *, DeclareData *,bool);
   void Insert_in_transition_list( Transition_block **, Place_block *); 
    void insert_in_null_always_list(struct alwaysblock_struct *); 
    void insert_in_operator_list( DeclareData *, Operate_op *,Signal_selector *,bool,Compare_operator *,bool);
    void Insert_in_compare_list(Compare_operator *,Compare_operator *);
    void Insert_datainput_in_placelist(Transition_block *,bool&,Graph_node *,State_var *);
    void Insert_in_equalto_list(Equal_to_op *,DeclareData *,Equal_to_op *);
    void Insert_place_in_list(DeclareData *, Place_block *);
    void Insert_in_parallel_place_list(Place_block *);
    void Insert_between_alwayslist(Always_block *,Always_block *,Graph_node *);
    void Insert_in_output_transition_list(DeclareData *,Transition_block *);
    void Insert_var_list(DeclareData *,DeclareData *);
    void Insert_selector_list(State_var *,Signal_selector *);
   void Insert_port_input(ModuleInstantiate*& , Graph_node *);
   void Insert_operator_type(Graph_node *);
   void Insert_else_block(Always_block*& , Ifthenelse_block *);
   
    
   void Create_node_items(Graph_node * , struct FSM_struct *,bool); 
  void Create_DFG_from_Caseblock( DFG_block **, struct casestatement_struct *, struct declare_data **,Graph_node *,State_var *,bool,DeclareData *,bool,DeclareData *); 
 void Create_DFG_from_assignexpr( DFG_block *, struct assignmentvar_struct *, struct declare_data*& ,Graph_node *,State_var *,bool,bool); 
 void Create_DFG_from_operateexpr( DFG_block *, struct operation_struct *, struct declare_data *,bool,bool); 
  void Create_DFG_from_complexexpr(DFG_block *,struct alwaysblock_struct *, struct declare_data *); 
  void Create_DFG_from_FU( struct node_struct *, DFG_block *, Place_block *, struct instantiate_module *,Graph_node *,State_var *);
  void Create_DFG_from_ifthenelse( DFG_block *dfgnode , struct ifthenelse_struct *condexpr , struct declare_data *,Graph_node *,State_var *,bool,struct declare_data *,Ifthenelse_block *,bool);
void Create_node_in_Transition_block( Transition_block **, struct alwaysblock_struct *,Graph_node *,State_var *,bool,bool,DeclareData *,Ifthenelse_block *,DeclareData *); 
void Create_search_list(DeclareData *, Operate_op *,Place_block *,int&);
//void Create_source_code(bool);
void Create_path_loop(DeclareData *, Graph_node *,State_var *,DeclareData*& );
bool Check_State_list(State_var **,DeclareData *,Place_block*&,int );
void Create_and_attach_cond(Ifthenelse_block *, Graph_node *);
bool Check_always_node(Always_block*& );

 void attach_transition_nodes(Place_block *, bool , Always_block *,Graph_node *,State_var *,bool,DeclareData *,Ifthenelse_block *,bool,DeclareData *); 
 void Attach_AssignNode_toDFG( DeclareData *,bool,Graph_node *,State_var *,Compare_operator*& ,bool,bool);
 void Attach_condvar_to_node(Place_block *);
 void Attach_clocked_transitions(Graph_node *,State_var *,bool);
void attach_nodes_of_Loop(Place_block*& ,Transition_block*& ,Equal_to_op*& ,Operate_op*& ,Path_node *,Graph_node *,State_var *first_state,DeclareData*& ,bool ,DeclareData *,DeclareData*&,DeclareData *);
void Attach_first_node_in_Loop(DeclareData*& ,struct PathList_struct *);

bool Search_OutputVarFrom_Places( DeclareData *, Place_block * , Transition_block *& , Place_block *& , DFG_block *,DeclareData *&,Graph_node *,State_var *,bool,bool& ,bool);
bool Search_var_InStateList(DeclareData * , State_var *);
void Search_varFrom_FU_Modules(ModuleInstantiate *, Place_block *,Graph_node *,State_var *,bool);
 void search_for_always_node(struct node_struct *, bool, bool); 
 void search_graph_FORloop(Graph_node *,State_var *,Place_block *);
 bool Search_transition(Place_block *, Transition_block *&,DeclareData *,Operate_op *&, int,bool,Operate_op *);
void Search_outputvar_from_ClockTransition(DFG_block *);
bool Search_placeInput(Place_block *, Operate_op *);
bool Search_var_from_graph(DeclareData *,DeclareData *,Transition_block *,Compare_operator*& ,Signal_selector*& , Operate_op*& ,DeclareData*& ,State_var *,bool,bool);
bool Search_var_from_prev_op( Operate_op*& , Operate_op * , DeclareData *);
bool Search_comp_from_comparator_list(Operate_op *,int,bool);
bool Search_var_from_statelist( DeclareData * , State_var *&,bool);
Place_block *Search_place_of_input(State_var *,bool,Place_block *,DeclareData *,DeclareData*&,bool, DeclareData *);
bool Search_in_equalto_list(DeclareData *,DeclareData *&);
bool Search_ifthenelse_list(Ifthenelse_block *, DeclareData *, Ifthenelse_block*&);
bool Search_assign_list(DeclareData *,Graph_node *,DeclareData*&, Operate_node*&);
bool Search_Always_list(Always_block *,DeclareData *, Always_block*&);
bool Search_varassign_list(Assign_var *, DeclareData *, Assign_var*&);
bool Search_ModuleInst_list( ModuleInstantiate *,DeclareData *,ModuleInstantiate*&);
bool Search_operation_list(Operate_node *, DeclareData *,Operate_node*&,ComplexOp_node *,ComplexOp_node*&);
bool Search_output_from_node_list(DeclareData *);
bool Search_back_parse_tree(DeclareData *,DeclareData *,Graph_node * , int&,bool,bool,bool,DeclareData** ,int);
bool Search_node_from_clocked_transition(Always_block *, Transition_block*& );
bool Search_node_Loop(Always_block *, DeclareData *,ModuleInstantiate *,Assign_var *,DeclareData*& );
bool Search_depth_OutputVarFrom_Places(DeclareData *,DeclareData *,Graph_node *,State_var *,bool ,bool ,DeclareData*& ,Transition_block*&,Place_block *,DFG_block *,bool,bool,DeclareData** );
bool Search_input_in_graph(DeclareData*& ,State_var *);
bool Search_in_Cond_Block(DeclareData *, Ifthenelse_block *);
bool Search_var_in_CaseBlock(DeclareData *, Case_Statement *);



void Initialize_structures( Condition_block *, DFG_block *, Place_block *,Operate_op *,Equal_to_op *,Path_node *);
void Initialize_nodes(Signal_selector *,Compare_operator *,State_var *,struct control_struct *,struct BasicBlock_Struct *,struct multiplexer_struct *);
void Initialize_control_pointers(struct control_struct** ,int );
void Initialize_char(const char **,int);

void Copy_block_to_node(Ifthenelse_block *&, Ifthenelse_block *, PortList *,Operate_node *&,Operate_node *,bool);

DeclareData *Get_var_from_comparator(Operate_op *);

bool Check_state_of_input(Place_block *, Place_block *);

void Replace_ports_list(Always_block *,PortList *&,DeclareData *,bool,Operate_node *,Graph_node *);

bool Trace_Output_for_State_Place(DeclareData *,State_var *&);

void Modify_ports_list(PortList*& ,Always_block *);

void Delete_node_list();
void Delete_always_node(Graph_node *,Always_block*& ,bool ,Ifthenelse_block*& ,ModuleInstantiate*& ,bool,Operate_node*& );
void Delete_assign_node(Graph_node *,Assign_var*& );
void Delete_case_node(Always_block*& ,DeclareData *,Graph_node *,Ifthenelse_block*& );
void Delete_var_node(DeclareData*& );
void Delete_graph_nodes(Graph_node *);
#endif














