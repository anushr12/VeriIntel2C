#ifndef ANALYSIS_PARSE_H
#define ANALYSIS_PARSE_H

#ifdef VERIFIC_NAMESPACE
using namespace Verific ;
#endif



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
//#include "petri_graphTransform.h"
typedef enum type_d { array , reg, var , wire , integer , parameter , input, output}type_d;

/* structures of different nodes*/

/* data declaration node */
// the operator_out part is already recognized in dfg node this declaredata is associated with but equal_op_out is not with any dfg so its recognized separately
typedef struct declare_data{

  int bit_width;
  bool array; //VeriVariable->IsArray()
//  bool next_operator_out; //for checking if there is more than one operator attached
  //bool next_selector_out; //for checking if there is more than one signal selector attached
 // bool next_comparator_out;
  type_d data_type; // VeriVariable->IsType() , mention if it is input type
  const char *name;
  int dimensions;
  unsigned unary_operator;
  struct operate_op_struct *operator_in;
  struct operate_op_struct *operator_out;
  struct signal_select_struct *signal_selector_out; //pointing to the signal selector
  struct equal_to_struct *equal_op_out; //pointing to assignto equal operator
  struct Compare_op_struct *comparator_out; //pointing to comparator
  struct trans_struct *transition_out;
  struct place_struct *place_ptr;
  struct DFG_struct *dfgnode_out;
  struct declare_data *next_n;
  struct declare_data *prev_n;
  
}DeclareData;



typedef struct ports_list{
  //const char *port_name;
  DeclareData *first_port;
  DeclareData *prev_p;
  DeclareData *next_p;
}PortList;



/* module instantiation */
typedef struct instantiate_module{

  const char *mod_name;
  char optype; //operator type of the FU module
  struct ports_list *ports_list; //list of input pointers
  //struct ports_list *input_list; //list of input pointers
  //struct ports_list *output_list; //list of output pointers
  struct instantiate_module *nextm;
  struct instantiate_module *prevm;
  // struct instantiate_module *first_module;

}ModuleInstantiate;

  
  
  
//op
typedef struct operation_struct{
  
  struct ports_list *input_list;
  DeclareData *output;
  unsigned operator_type;
  unsigned unop_type; //if the operation is part of the unary operator
  struct operation_struct *prev_op;
  struct operation_struct *next_op;
  //struct operation_struct *first_opnode;
}Operate_node;

//combined operations
typedef struct complex_operation_struct{
  Operate_node *basic_op1;
  Operate_node *basic_op2;
 // struct complex_operation_struct *complex_op;
  DeclareData *basic_operand;
  DeclareData *out_value;
  unsigned operator_type;
  struct complex_operation_struct *prev_op;
  struct complex_operation_struct *next_op;
  }ComplexOp_node;
  


// for the functional units
typedef struct Functional_operator_mod{
  const char *name;
  PortList *input_list;
  PortList *output_list;
  Operate_node *operation;
  }Func_opmodule;

typedef struct assignmentvar_struct{
  
  DeclareData *left_value;
  DeclareData *right_value;
  //Operate_node *operation_rhs;
  struct assignmentvar_struct *next_n;
  struct assignmentvar_struct *prev_n;
}Assign_var;

typedef struct assignmentconst_struct{
  
  DeclareData *left_value;
  int const_value;
  const char *const_expr;
  struct assignmentconst_struct *next_n;
  struct assignmentconst_struct *prev_n;
}Assign_const;

typedef struct casestatement_struct{
  
  DeclareData *condition_var;
  //unsigned int case_value; //constant value ID_VERICONSTVAL
  char *case_value;
  Assign_const *expression_ct;
  Assign_var *expression_vt;
  struct casestatement_struct *next_n;
  struct casestatement_struct *prev_n;
}Case_Statement;



typedef struct ifthenelse_struct{
  
  DeclareData *if_condition_var;
  Assign_const *equal_condition; //alongwith ifcondition, if there exists a condition if a variables is equal to a value, its called equal_condition
  DeclareData *then_var; //if the resulting output is a control wire signal, then the output is just a variable i.e then_var
  Operate_node *in_control_operation; //this node is an operation(can be AND or OR) of the incoming control signals, this will have no output and only input list, only used when the rhs value of the statement is an operation
  Assign_var *then_expr_var; //this is the resulting assign expr,
  struct ifthenelse_struct *else_expr_block; //to store the else part of the ifthenelse expr
  struct ifthenelse_struct *next_block;
  struct ifthenelse_struct *prev_block;
}Ifthenelse_block;

typedef struct alwaysblock_struct{
  
  PortList *event_controls;
  Case_Statement *CaseBlock;
  Ifthenelse_block *CondBlock;
  Assign_var *assign_expr;
  Operate_node *operate_expr;
  ComplexOp_node *comp_expr;
  struct alwaysblock_struct *prev_n;
  struct alwaysblock_struct *next_n;
}Always_block;

// attach the first node of the different type node lists for one module

typedef struct node_struct{
  
  //struct node_struct *first_node;
  const char *name;
  struct node_struct *prev_node;
  struct node_struct *next_node;
  DeclareData *data_node;
  Ifthenelse_block *ifthenelse_node;
  Assign_var *varassign_node;
  Assign_const *constassign_node;
  Always_block *always_node;
 // Case_Statement *case_node;
  Operate_node *operation_node;
  //ComplexOp_node *complexop_node;
  ModuleInstantiate *module_inst_node;
}Graph_node;

// FSM state list 
typedef struct FSM_struct{

  struct FSM_struct *next_state;
  struct FSM_struct *prev_state;
  DeclareData *state_name;
//Compare_op_struct *comparator_out_signal; //the state name is having the comparator_out signal
  signal_select_struct *signal_selector_out;
  }State_var;



/*********end of structures***********/




/*Function declarations */

static void CreateModuleItems(VeriModuleItem *);
void CreateGraphNodes(VeriModuleItem *);
void Create_state_variables(VeriModuleItem *);
void Insert_in_state_list( State_var *,State_var*& );
void insert_port_list(const char *, ModuleInstantiate *, DeclareData *,Func_opmodule *,bool,bool);
void insert_in_list(PortList *, DeclareData *);
void insert_moduleInst_list(ModuleInstantiate *);
void insert_datanode_list( DeclareData *);
void insert_operation_list(Operate_node * , ComplexOp_node *,Graph_node *);
void Insert_in_always_list(Always_block *);
void insert_assign_list( Assign_var *, Assign_const *);
void insert_cond_list(Ifthenelse_block *,Graph_node *);
void Insert_event_controls(Always_block *);
void assign_value( DeclareData *, DeclareData *);
static void CreateNodesInAlwaysBlock(VeriStatement *, Always_block *,bool,bool& );
void InsertCaseInBlock( Always_block *, Case_Statement *);
void InsertOpInAlwaysblock(Always_block *, Operate_node *, Ifthenelse_block *);
void Initialize_values( ModuleInstantiate *,PortList *,Operate_node *,Assign_var *,Assign_const *,Case_Statement *,Ifthenelse_block *,Always_block *,DeclareData *,Graph_node * , ComplexOp_node * , struct trans_struct *);
void CreateComplexOperations( VeriExpression *, Ifthenelse_block*& , bool, unsigned,bool,int&,Operate_node*& );
void Insert_graphnode_list(Graph_node *,bool);

void Delete_list(PortList * , DeclareData *);
void Delete_cond_node(Ifthenelse_block *);
void delete_var_list(Graph_node *,DeclareData*& );
/*extern void insert_in_condition_list( Condition_block **, DFG_block **);
extern void Create_DFG_from_Caseblock( DFG_block **, Case_Statement *, DeclareData **);
extern void Create_DFG_from_assignexpr( DFG_block **, Assign_var *, DeclareData **);
extern void Create_DFG_from_operateexpr( DFG_block **, Operate_node *, DeclareData **);
extern void Create_DFG_from_complexexpr(DFG_block **,Always_block *, DeclareData **);
extern void Create_node_in_Transition_block( Transition_block **, Always_block *);
extern void Insert_in_transition_list( Transition_block **, Place_block *);
extern void attach_transition_nodes(Place_block *, bool);

extern int create_petri_graph(Graph_node *); 
extern void search_for_always_node(Graph_node *, bool, bool); 
extern void insert_in_null_always_list(Always_block *); 
extern void Select_from_operator_list(Operate_op *, unsigned);
*/


#endif  
  
  
  
  
  
