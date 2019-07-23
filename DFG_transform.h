

#ifndef DFG_TRANSFORM_H
#define DFG_TRANSFORM_H

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

#include "petri_graphTransform.h"

using namespace std;

#ifdef VERIFIC_NAMESPACE
using namespace Verific ;
#endif

typedef struct control_struct{
	struct BasicBlock_Struct *bb_ptr; //this ptr for storing the basic block connected with this control block
	State_var *state_node;                          //a single control node will contain a state_node or a control_dfgnode which is a dfg node that produces a control signal
	struct control_struct *next_control_block;
	struct control_struct *prev_control_block;
	DFG_block *control_dfg_node;  //this dfg node is a control operation node which produces a control signal equivalent to a state signal / control loop implemented using this
	Equal_to_op *eq_node; //this equal node is used for switch-case conditional nodes from petrigraph, when a comparator for the condition has been created
	Compare_operator *control_compare_node; //this node is a conditional control node which results a cntrl output depending on a condition
	Signal_selector *signal_select_node;
	DeclareData *control_in_from_dfg; //if a dataflow signal gives rise to control signal, then control_in_from_dfg shows the direction to this control node
	//struct control_struct *control_in; // if a control node gives rise to this control node,then control_in shows the direction to this control node
	struct control_struct *result_control; //this connects to this control node's child or children
	struct control_struct *control_in_pointers[10];
	DeclareData *control_out;
}Control_block;

//this structure is to represent case-statement conditional node, representing a multiplexer
typedef struct multiplexer_struct{
	DeclareData *enable_signal;
	Condition_block *cond_expr;
	DeclareData *output;
}Mux_node;

//this is for representing the data flow block where only the operations are stored and others are abstracted away
typedef struct BasicBlock_Struct{
	Control_block *control_node_pointers[10]; //this is the list to store the control blocks which point to this basic block
	
	//Operate_op *first_OperTree_node; //this is the root node of the basic block, if there are parallel operations, then the member "next_oper" will point to the next parallel 
	DeclareData *first_block_input; // this is the list of all inputs to this basic block(including the input data type nodes)
	
	DeclareData *first_block_output; //list of all the outputs of this block
	struct BasicBlock_Struct *next_block;
	struct BasicBlock_Struct *prev_block;
	Mux_node *multiplexer;
}Basic_block;


//to be used during transformation from petrigraph to DFG
typedef struct PathList_struct{

	DeclareData *varnode;
	Place_block *placenode;
	Transition_block *trannode;
	Operate_op *opnode;
	Equal_to_op *eqnode;
	Compare_operator *compnode;
	Signal_selector *signalnode;
	DFG_block *dfgnode;
	PathList_struct *next_node;

}Path_list;



/*function definitions*/

int Transform_to_flow_graph(State_var *, Place_block *,Place_block *, Equal_to_op *);
bool Trace_back_node(DeclareData *, State_var*&,State_var *,State_var *,State_var** ,bool,bool,DeclareData *,bool);
bool Trace_depthwise_node( DeclareData *, State_var *,State_var*&);
bool Trace_control_result(Path_list *,Path_list *,State_var *,Control_block *,bool,Basic_block*& );

bool Search_Header_of_loop(State_var *,Path_list*&,bool);
bool Search_dominator_of_node(DeclareData *,DeclareData *, Path_list*&,State_var *,State_var *,bool ,bool,bool,bool,Basic_block*&,DeclareData** ,Basic_block *);
bool Search_path_list(Path_list *,Place_block *,Transition_block *,Equal_to_op *,Operate_op *,DFG_block *,Compare_operator *, Signal_selector *);
bool Search_back_petri_model(DeclareData *,DeclareData *, bool,bool ,State_var *,int&,bool,Path_list*& ,bool,DeclareData**,int,bool,Basic_block*& ,bool,DeclareData*& );
bool Search_back_node(DeclareData *,DeclareData *,State_var *,State_var *,Place_block*&,Transition_block*&,Equal_to_op*&,Operate_op*&,Compare_operator*&, DFG_block*&,Signal_selector*&);
bool Search_end_node_BasicBlock(DeclareData *, Basic_block *, DeclareData*& , Control_block*&,bool, Basic_block*&,bool, DeclareData *);
bool Search_control_nodes(DeclareData *, Control_block*&, DeclareData*& , DeclareData *,Control_block *);
bool Search_state_from_controlnode_list(State_var *,Control_block *, Control_block*& );
bool Search_ControlNodes_depthwise(DeclareData *,Path_list*& ,bool,bool,Path_list *,bool,Path_list*& ,bool );
bool Search_from_control_block(Compare_operator *,Signal_selector *,Control_block*&);
bool Search_header_in_nodepath(Path_list *,DeclareData *,Path_list*&);
bool Search_in_list(Compare_operator *, Signal_selector *,DFG_block *,Operate_op *,Path_list *);
bool Search_back_BasicBlock_node(DeclareData *,DeclareData *,Basic_block *,Equal_to_op*&,Operate_op*& );
bool Search_loop_for_node( int ,DeclareData *,DeclareData*& );
bool Search_exitpoint_DataLoop(DeclareData *, DeclareData** ,int,Path_list*& );
bool Search_node_in_PortList(DeclareData *,Basic_block *,bool);
bool Search_node_in_DataLoop(DeclareData *,DeclareData *,DeclareData*& ,Path_list*& );
bool Search_node_in_Control_Loop(DeclareData *, DFG_block *, DeclareData*&);
bool Search_state_in_list(State_var *,DeclareData *, State_var** ,int);
void Search_comp_SS_path_subfunction(bool& ,bool& ,DeclareData *,Path_list*& ,Basic_block *,State_var *,Control_block *,bool,State_var** ,State_var *);
bool Search_state_of_OperatorInput(Control_block *,Operate_op *, DeclareData *,State_var *,Signal_selector *,Control_block*& );
bool Search_var_in_InputList(DeclareData *, Place_block *,Transition_block *);
bool Search_back_loop(DeclareData *,DFG_block *,DeclareData *,DeclareData*& );
bool Search_BasicBlock_from_control_list(Basic_block *, Control_block *,Control_block*& );
void Search_header_in_looplist(Path_list *, Path_list*& , Path_list*&,bool,int& );
bool Search_output_of_LoopList(DeclareData *, Place_block*& );
bool Check_node_out(DeclareData *, DeclareData *);

void Create_nodes_for_conditional_block(DeclareData *, Condition_block *, State_var *,Control_block*& , Control_block*&,Basic_block*& );
void Create_control_node(Control_block*& ,DeclareData*&,Compare_operator *,Control_block*& ,State_var *,Control_block*& ,Signal_selector *,Condition_block *,Equal_to_op *,bool);
void Create_subnodes_under_endnode( DeclareData*& , DeclareData *, Control_block*& ,Basic_block *,Place_block *, Basic_block*& ,Equal_to_op*& ,Equal_to_op *,Operate_op*& ,Operate_op *,bool, char);
void Create_control_loop_block(Control_block*& ,Path_list *);
bool Check_state_of_place_input( Place_block *, DeclareData *, State_var *, Transition_block *,State_var *,State_var **,int , Control_block*&);
bool Check_exitpoint_of_loop(Path_list *, Path_list *,Path_list *,Path_list*& ,Path_list*& ,bool,bool);
bool Check_parent_nodes(DeclareData *,State_var *,Control_block *,Control_block*& ,DeclareData*& ,Basic_block*& );
bool Check_creation_of_path(DeclareData *,DeclareData *,DeclareData*&);
bool Check_loop_body(DeclareData *,State_var *,bool& ,bool& ,Path_list*&,bool,DeclareData*&,Control_block*&,bool,Path_list*&,bool,Place_block*& ,DeclareData *,Control_block *);
void Connect_control_loopto_controlnode_check(Control_block *,Path_list *,Path_list *,Path_list *);
bool Check_node_from_array(DeclareData** , int,DeclareData *);
void Change_node_in_array(DeclareData**, int ,DeclareData *,bool);
void Create_loop_body_control_subfunction(Control_block*& ,Path_list *,DeclareData*&,DeclareData *,int  );
void Create_dataflow_unrolled(Place_block *, Equal_to_op *, State_var *);
void Create_control_and_basic_blocks(State_var *, DeclareData *,bool ,bool ,State_var *,Control_block*&);
void Create_fully_unrolled_graph(Equal_to_op *);


bool Find_earlier_state(State_var*&,State_var *, Control_block *);

void Insert_in_control_list(Control_block*& , Control_block *);
void Insert_in_child_list( Control_block *, Control_block *);
void Insert_in_node_list(DeclareData *, DeclareData *);
void Initialize_array_pointer(Path_list *);
void Initialize_array(DeclareData** ,int );
void Initialize_StateArray(State_var** ,int);
void Insert_path_in_BasicBlock(Control_block *,Basic_block *, DeclareData *,State_var *,DeclareData *,bool);
void Insert_in_BasicBlock_list(Control_block *, Basic_block *);
void Insert_in_pathlist_list(Path_list*&, Place_block *,Transition_block *,Equal_to_op *,Operate_op *,Compare_operator *,DFG_block *, Signal_selector *);
void Insert_in_StateArray_list(State_var *,State_var**,int);
void Insert_node_in_pathlist(Path_list*& ,Path_list *);
void Insert_in_BasicBlock_array(Basic_block *, int,Control_block *);
void Insert_in_Controls_array(Control_block *,int,Control_block *);
void assign_controls(State_var *, State_var *, Equal_to_op *, Equal_to_op *,bool);


void delete_loop_list(void);
void delete_node_list(Path_list*& );
void Delete_looplist_nodes(void);

void Get_cond_from_dfgnode(DFG_block *,DeclareData *,Condition_block*& );

#endif





