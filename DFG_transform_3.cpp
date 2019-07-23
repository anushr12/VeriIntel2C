#include <iostream>
#include <new>
#include <stdio.h>
#include <string.h>


#include "Array.h"          // Make dynamic array class Array available
#include "Map.h"            // Make associated hash table class Map available
#include "Strings.h"        // A string utility/wrapper class

#include "Message.h"        // Make message handlers available, not used in this example

#include "veri_file.h"      // Make Verilog reader available

#include "VeriModule.h"     // Definition of a VeriModule and VeriPrimitive
#include "VeriId.h"         // Definitions of all identifier definition tree nodes
#include "VeriExpression.h" // Definitions of all verilog expression tree nodes
#include "VeriModuleItem.h" // Definitions of all verilog module item tree nodes
#include "VeriStatement.h"  // Definitions of all verilog statement tree nodes
#include "VeriMisc.h"       // Definitions of all extraneous verilog tree nodes (ie. range, path, strength, etc...)
#include "VeriConstVal.h"   // Definitions of parse-tree nodes representing constant values in Verilog.
#include "VeriScope.h"      // Symbol table of locally declared identifiers
#include "VeriLibrary.h"    // Definition of VeriLibrary
#include "veri_yacc.h"
//#include "analysis_parse.h"
//#include "petri_graphTransform.h"

#include "DFG_transform.h"


using namespace std;

#ifdef VERIFIC_NAMESPACE
using namespace Verific ;
#endif

Control_block *first_control_node;
Basic_block *first_basic_block;
Mux_node *first_mux;
DeclareData *program_inputs; //these are the actual input variables to the verilog code
Path_list *loop_list[10];

int Transform_to_flow_graph(State_var *first_state, Place_block *first_place_node,Place_block *first_parallel_place, Equal_to_op *first_EqualTo_node){


	//if(first_EqualTo_node || first_parallel_place)
		// there are unrolled paths in this graph (full or partial)
		//this fn also includes unroll 0 feature
		Create_dataflow_unrolled(first_parallel_place,first_EqualTo_node,first_state);
//	else
	//	Create_dataflow(first_state,first_place_node);

}


void Create_dataflow_unrolled(Place_block *first_parallel_place, Equal_to_op *first_EqualTo_node, State_var *first_state){

Equal_to_op *first_n=NULL;
bool state_exists = false;
State_var *statenode=NULL;
Place_block *tmp_p=NULL;
Control_block *control_search=NULL;
Transition_block *trans_p = NULL;
State_var *tmp_state=NULL;
bool node_down = false;
DeclareData *state = NULL;
DeclareData *varstart = NULL;

//if state_exists is false, then the state found does not exist currently as a control block, thus create a control block n then put the path in its associated basic blk
// if state_exists is true, then the state exists already as a control block, thus search the control block list for the statenode name and insert the path in its associated blk
//with this combination, if statenode exists, then there exists some state, but if no statenode, then there is no state for that path and then call Create_fully_unrolled_Graph

	if(first_EqualTo_node){
	
		// these nodes do not go inside any control block. Now,search depthwise for each parallelequalto node if its associated with any state
		first_n = first_EqualTo_node;
		while(first_n){
			//here we check if statenode is already exisitng asa control block
			state_exists = Trace_depthwise_node(first_n->lhs_value, first_state,statenode);
			if(state_exists){
				//this means that there is a state attached in the path of the first_n
				Create_control_and_basic_blocks(statenode, first_n->rhs_value,false,true,first_state,control_search);
			}
			else if(!state_exists && statenode)
				Create_control_and_basic_blocks(statenode,first_n->rhs_value,true,true,first_state,control_search);
			else{
				// this case shows that there are no any states in the path of this equalto node, which implies all the equalto nodes do not have a state, so the entire graph is built inside a single basic block
				Create_fully_unrolled_graph(first_EqualTo_node);
				break;
			}
			first_n = first_n->next_equal;
		}
	
	}
	//parallel_place means its created because there is a "input" type rhs_value to this place
	else if(first_parallel_place){
		tmp_p = first_parallel_place;
		while(tmp_p){
			if(tmp_p->state_place_input){
				//this means the input to this place is only one input and its data type is input
				state = tmp_p->state_place_input;
				//no state has not yet been made
				if(Search_var_from_statelist( state,statenode,false)){
					if(Search_state_from_controlnode_list(statenode,first_control_node,control_search))
						Create_control_and_basic_blocks(statenode,tmp_p->first_place_input,false,false,first_state,control_search);
					else	Create_control_and_basic_blocks(statenode,tmp_p->first_place_input,true,false,first_state,control_search);
				}
					
			}
			else{
				
				varstart = tmp_p->first_place_input;
				while(varstart){
					if(!strcmp(varstart->name,tmp_p->first_trans_node->data_node->condition_op->assign_expr->rhs_value->name))
						break;
					varstart = varstart->next_n;
				}
				
					if(varstart && Trace_depthwise_node(tmp_p->first_trans_node->output_var,first_state,statenode)){
						//equalnodes dont exist in this case
						if(Search_state_from_controlnode_list(statenode,first_control_node,control_search))
							Create_control_and_basic_blocks(statenode , varstart,false,false,first_state,control_search);
						else	Create_control_and_basic_blocks(statenode ,varstart,true,false,first_state,control_search);
					}	
					//no else condition
					//trans_p = trans_p->next_trans_node;
				//}
			}
			tmp_p = tmp_p->next_place;
		}
		
	}
	else{
		//UNROLL 0 CASE FOR NOW
		//in this case, there are no equal nodes or parallel place. Thus its unroll0/unroll partial
		//EDIT HERE FIRST before level 2 ------ LEVEL 1
		//start from first_state and then go depth wise to all the places connected to the state
		tmp_state = first_state;
		while(tmp_state){
			state = tmp_state->state_name;
			while(state){
				if(state->place_ptr){
					node_down = true;
					tmp_p = state->place_ptr;
					while(tmp_p){
						trans_p = tmp_p->first_trans_node;
						//here we dont check Trace_depthwise because here it is already known its connected to tmp_state
						if(Search_state_from_controlnode_list(tmp_state,first_control_node, control_search))
							Create_control_and_basic_blocks(tmp_state, trans_p->data_node->assignment_graph->rhs_value,false,false,first_state,control_search);
						else 
							Create_control_and_basic_blocks(tmp_state,trans_p->data_node->assignment_graph->rhs_value,true,false,first_state,control_search);
						tmp_p = tmp_p->next_place;
					}
					if(node_down) break;
				}
				if(!node_down && state->equal_op_out){
					state = state->equal_op_out->lhs_value;
					node_down = false;
				}
				if(!node_down) state = NULL;
			}
			tmp_state = tmp_state->next_state;
		}
	}

}

//fn to create the graph inside a single basic_block only if its detected that the graph is unrolled full withoutany states and places
void Create_fully_unrolled_graph(Equal_to_op *eq_first){

DeclareData *tmpnode = NULL;
Equal_to_op *tmpeq = NULL;
Basic_block *block_new = NULL;

block_new = new Basic_block;
Initialize_nodes(NULL,NULL,NULL,NULL,block_new,NULL);

if(!first_basic_block)
	first_basic_block = block_new;
else Insert_in_BasicBlock_list(NULL,block_new);


while(tmpeq){

	tmpnode = tmpeq->rhs_value;
	 Insert_path_in_BasicBlock(NULL,block_new,tmpnode,first_state,NULL,false);
	 
	tmpeq = tmpeq->next_equal;
}

//put the input/output of basic block - already put in basic block fn


}




//function to create the control block nodes of (state) and insert the path starting from pathnode,
//equalnodes_exist is to indicate if this function is called when equalnodes exist, n if its false, then its called when equalnodes do not exist
void Create_control_and_basic_blocks(State_var *state , DeclareData *pathnode,bool control_create,bool equalnodes_exist,State_var *first_state,Control_block*& search_control){

Control_block *control=NULL;
State_var *tmpstate = NULL;

bool nodefound=false;

//this case is to run only for the first time, irrespective of control_create is true or false. all the state control nodes are created in this case
if(first_state && !first_control_node){
		tmpstate = first_state;
		while(tmpstate){
			control = new Control_block;
			Initialize_nodes(NULL,NULL,NULL,control,NULL,NULL);
			control->state_node = new State_var;
			Initialize_nodes(NULL,NULL,control->state_node,NULL,NULL,NULL);
			control->state_node->state_name = new DeclareData;
			assign_controls(control->state_node,tmpstate,NULL,NULL,true);
			if(!first_control_node) first_control_node = control;
			else
				Insert_in_control_list(first_control_node,control);
		
			tmpstate = tmpstate->next_state;
		}
}


if(control_create && equalnodes_exist){
	//create a control block associated with the statenode
	// since, the control block will b created, the starting node pathnode, shall be the inputs to the associated basic block
	
		if(Search_state_from_controlnode_list(state,first_control_node,control)){
			control->bb_ptr = new Basic_block;
			Initialize_nodes(NULL,NULL,NULL,NULL,control->bb_ptr,NULL);
			Insert_in_BasicBlock_list(NULL,control->bb_ptr);
			Insert_path_in_BasicBlock(control,control->bb_ptr,pathnode,first_state,NULL,false);
			//(first_control_node , control);
		}
	
}
else if(!control_create && equalnodes_exist){
	//state exists as a control_block
	//first find, the control_block which has "state"
	control = first_control_node;
	while(control){ 
		if(!strcmp(control->state_node->state_name->name , state->state_name->name)){
			nodefound = true;
			break;
		}
		else control = control->next_control_block;
	}
	if(nodefound){
		if(!control->bb_ptr){
			 control->bb_ptr = new Basic_block;
			 Initialize_nodes(NULL,NULL,NULL,NULL,control->bb_ptr,NULL);
			 Insert_in_BasicBlock_list(NULL,control->bb_ptr);
		}
		Insert_path_in_BasicBlock(control,control->bb_ptr,pathnode,first_state,NULL,false);
	}
		
}
else if(control_create && !equalnodes_exist){
	//in this situation, unroll 0 case comes. but control node is to be created newly.
	
	//first check, if the state has been created as a control block already
	//in this case, we have to check in the depthwise path until which node, does the state remains the same
	if(Search_state_from_controlnode_list(state,first_control_node,control)){
		control->bb_ptr = new Basic_block;
		Initialize_nodes(NULL,NULL,NULL,NULL,control->bb_ptr,NULL);
		Insert_in_BasicBlock_list(NULL,control->bb_ptr);
		Insert_path_in_BasicBlock(control,control->bb_ptr,pathnode,first_state,NULL,false);
		//Insert_in_control_list(first_control_node , control);
		
	}
}
else if(!control_create && !equalnodes_exist){
	
	if(search_control)
		Insert_path_in_BasicBlock(search_control,control->bb_ptr,pathnode,first_state,NULL,false);

}
	//LEVEL 2
	
}



//function to search the state of the other input of opnode, not tmp1, check the state of other inputs of comparator, signal selector
bool Search_state_of_OperatorInput(Control_block *control,Operate_op *opnode, DeclareData *tmp1,State_var *first_state,Signal_selector *select_check,Control_block*& controlprev){

DeclareData *tmp2=NULL;
State_var *state_res=NULL;
State_var *state_list[10];
Control_block *control_ret = NULL;
int i=0;
State_var *tmps=NULL;
bool search=false;
//first get the input of opnode which is not tmp1
if(opnode){
	if(!strcmp(opnode->op1->name , tmp1->name))
		tmp2 = opnode->op2;
	else tmp2 = opnode->op1;

	if(Trace_back_node(tmp2 , state_res,first_state,NULL,state_list,true,true,NULL,true)){
		
		while(state_list[i]){
			if(control->state_node && !strcmp(state_list[i]->state_name->name , control->state_node->state_name->name)){
				search = true;
				break;
			}
			else if(Search_state_from_controlnode_list(state_list[i],first_control_node,control_ret)){
				controlprev = control_ret;
				search = true;
				break; 
			}
			else search = false;
			i++;
				//tmps=tmps->next_state;
		}
		//}
		if(state_res){
			if(!strcmp(state_res->state_name->name,control->state_node->state_name->name))
				search=true;
		}
	}
	else search = false;
}


return search;
}

//REFERENCE 1
//now trace this tmp if its going to a SS or a place
	//if going to a SS, then create a control block, with the output of the comparator.Then trace the output of the SS to check which  place is it controlling.
	//if going to a place directly, then check the state the comparator is connected with. If no, then check the state the place is connected with. Search the related basic block for the place->transition->datagraph->rhs_value. Then insert the place node.
//REFERENCE 2
//now trace tmp if it has further control nodes create it.else trace it further to search for any dataflow nodes if yes,insert them in basic_blocks,
		//the outer loop is to make it continue for signal_selector and comparator both
		
//REFERENCE 3
//this is for switch case
	//in this case, the dfgnode_condition_var is the only control input to the dfg. it must be implemented by either a control loop or inside basic block as a part of dataflow loop or normal endnode.
	//first create the comparator for each condition, and an equal node for the assign_expr and the output of the comparator is the rhs_value of the assign expr(endnode).
	

//this function is to check which basic block has the node which is controlled by the comp/SS/DFG/lop operatenode which is now stored in control_out
//if its not created ,then the newly made controlflow loop block will have its own basic block.
//SS can also lead to a comparator which will indirectly lead to a dataflow block. In this case, the SS will also be created as a control node

//control_out is the petrigraph node which is connected to a comparator/SS/DFG
//loop_control is the control block in which control_loop->control_dfg_node
//control_checkflag is the flag to indicate if the fn has been called for implementing controlnode_check nodes or its previous parent nodes. if true, means implement controlnode_check nodes but if false, only create parent nodes
bool Trace_control_result(Path_list *exitnode,Path_list *control_out,State_var *first_state,Control_block *loop_control,bool control_checkflag,Basic_block*& basicblock_loop){

DeclareData *tmp=NULL;
DeclareData *endnode_actual=NULL;
DeclareData *tmpvar=NULL , *var = NULL, *var_next=NULL;
DeclareData *tmpout=NULL;
DeclareData *endnode=NULL;
DeclareData *tmp_null=NULL;
DeclareData *endnode_cntrl = NULL;
Control_block *controlnode=NULL;
Control_block *cntrl_empty=NULL;
Control_block *control_prev=NULL;
Control_block *tmp_control=NULL;
Control_block *control_new=NULL;
Place_block *tmp_place = NULL;
Condition_block *tmpcond = NULL;
Equal_to_op *equalnode = NULL;
Operate_op *tmpop = NULL;
State_var *tmpstate=NULL;
Basic_block *block_ret = NULL;
Basic_block *block_null = NULL;
bool place_done=false;
bool stateflag=false;
bool control_create=false;
bool control_done=false;
bool path_done=false;
bool done = false;
bool loop_start = false;
bool flag = true;
bool check = false;

//tmp_control is control node created if the control loop has a comparator attached to it
//while going depthwise, this tmp_control might be connected to further signal selectors or comparators
if(control_out->compnode || control_out->signalnode || control_out->opnode){
	if(control_out->compnode)	
		tmpout = control_out->compnode->value_out;
	else if(control_out->signalnode)
		tmpout = control_out->signalnode->out_signal;
	else if(control_out->opnode)
		tmpout = control_out->opnode->output_value;
	//REFERENCE 1
	if(control_out->compnode){
		if(control_out->compnode->state_condition && Search_state_from_controlnode_list(control_out->compnode->state_condition,first_control_node,control_prev)){
			//control_prev is the state control node whose successor will be tmp_control
			Create_control_node(tmp_control,control_prev->state_node->state_name,control_out->compnode,control_prev,first_state,loop_control,NULL,NULL,NULL,false);
			//tmp_control->control_out = new DeclareData;
			//Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,tmp_control->control_out,NULL,NULL,NULL);
			//loop_control will be modified in the above function itself
			control_done=true;
		}
		 if(!control_done && control_out->compnode->condition_value){
			//if there is no state attached control_new is not created
			if(Search_end_node_BasicBlock(control_out->compnode->condition_value,first_basic_block,endnode,controlnode,true,block_ret,false,NULL)){
				control_done=true;
				if(!control_done && control_out->compnode->state_condition)
					Create_control_node(tmp_control,endnode,control_out->compnode,cntrl_empty,first_state,controlnode,NULL,NULL,NULL,false);
				else{	
					tmp_control->control_in_from_dfg = endnode;
					if(controlnode->control_out) controlnode->control_out->comparator_out= tmp_control->control_compare_node;
					else controlnode->control_out = endnode;
				}
				
			}
			else if((!control_done && control_out->compnode->state_condition) && Search_control_nodes(NULL,control_prev,endnode_cntrl,control_out->compnode->condition_value,NULL)){
			
				Create_control_node(tmp_control,endnode_cntrl,control_out->compnode,cntrl_empty,first_state,control_prev,NULL,NULL,NULL,false);
				control_done=true;
			}
		
		 }
	 }
	 if(control_out->signalnode){
	 	
	 	tmpvar= control_out->signalnode->state_in_signal;
	 	while(tmpvar){
	 		if(Search_var_from_statelist(tmpvar,tmpstate,false) && Search_state_from_controlnode_list(tmpstate,first_control_node,control_prev)){
	 			control_done = true;
	 			if(tmpvar == control_out->signalnode->state_in_signal)
		 			Create_control_node(tmp_control,control_prev->state_node->state_name,NULL,control_prev,first_state,loop_control,control_out->signalnode,NULL,NULL,false);
		 		else{
		 			if(!control_prev->result_control) control_prev->result_control = tmp_control;
		 			else Insert_in_child_list(control_prev->result_control,tmp_control);
		 			if(!tmp_control->control_in) tmp_control->control_in = control_prev;
		 			else Insert_in_child_list(tmp_control->control_in,control_prev);
		 			if(!control_prev->control_out->signal_selector_out) control_prev->control_out->signal_selector_out = tmp_control->signal_select_node;
		 			else insert_in_operator_list(control_prev->control_out,NULL,tmp_control->signal_select_node,false,NULL,false);
		 		}
	 		}
	 		else {control_done = false;break;}
	 		tmpvar = tmpvar->next_n;
	 	}
	 	tmpvar = control_out->signalnode->in_signal_list;
	 	//if atleast one state is attached, control_new is created and control_done is true
	 	while(tmpvar){
	 		if((control_done || !control_out->signalnode->state_in_signal) && Search_end_node_BasicBlock(tmpvar,first_basic_block,endnode,controlnode,true,block_ret,false,NULL)){
	 			control_done=true;
	 			if(tmpvar == control_out->signalnode->in_signal_list)
	 				Create_control_node(tmp_control,endnode,NULL,cntrl_empty,first_state,controlnode,control_out->signalnode,NULL,NULL,false);
	 			else{
	 				if(controlnode->control_out) controlnode->control_out->signal_selector_out = tmp_control->signal_select_node;
	 				else controlnode->control_out = endnode;
	 				tmp_control->control_in_from_dfg = endnode;
	 			}
	 		}
	 		else if( control_done || !control_out->signalnode->state_in_signal && Search_control_nodes(NULL,control_prev,endnode_cntrl,tmpvar,NULL)){
	 			Create_control_node(tmp_control,endnode_cntrl,NULL,cntrl_empty,first_state,control_prev,control_out->signalnode,NULL,NULL,false);
	 			control_done=true;
	 		}
	 		
	 		tmpvar= tmpvar->next_n;
	 	}
	 	
	 }
	 //its a gop or lop op node
	 if(control_out->opnode){
	 	//if its an opnode, then no separate control_node required to make .just create this node and and then proceed to the while loop below.
	 	control_done = true;
	 	if(control_out->opnode->op1->data_type!=integer)
	 		tmpvar = control_out->opnode->op1;
	 	else tmpvar = control_out->opnode->op2;
	 	if(Search_control_nodes(NULL,control_prev,endnode_cntrl,tmpvar,NULL)){
	 		endnode_cntrl->operator_out = new Operate_op;
	 		Initialize_structures(NULL,NULL,NULL,endnode_cntrl->operator_out,NULL,NULL);
	 		endnode_cntrl->operator_out->output_value = new DeclareData;
	 		assign_value(endnode_cntrl->operator_out->output_value,control_out->opnode->output_value);
	 		if(control_out->opnode->op1->data_type!=integer){
		 		endnode_cntrl->operator_out->op1 = endnode_cntrl;
		 		endnode_cntrl->operator_out->op2 = new DeclareData;
		 		assign_value(endnode_cntrl->operator_out->op2,control_out->opnode->op2);
		 	}
		 	else{
		 		endnode_cntrl->operator_out->op2 = endnode_cntrl;
		 		endnode_cntrl->operator_out->op1 = new DeclareData;
		 		assign_value(endnode_cntrl->operator_out->op1,control_out->opnode->op2);
		 	}
			if(loop_control == control_prev){
		 		if(!control_prev->control_out) control_prev->control_out = endnode_cntrl->operator_out->output_value;
		 		else Insert_var_list(control_prev->control_out,endnode_cntrl->operator_out->output_value);
		 	}
	 	}
	 	else control_done = false;
	 	
	 }
	//REFERENCE 2
	do{
		tmp = tmpout;
		check = false; flag = true;
		while(tmp && control_done){
			if(tmp->place_ptr){

				tmp_place = tmp->place_ptr;
				while(tmp_place && Search_var_in_InputList(tmp,tmp_place,NULL)){
					var = tmp_place->first_trans_node->data_node->condition_op->assign_expr->rhs_value;
					var_next = tmp_place->first_trans_node->output_var;
					if(Search_end_node_BasicBlock(var,first_basic_block,endnode,controlnode,true,block_ret,false,NULL)){
						if(Check_creation_of_path(endnode,var_next,endnode_actual)){
							basicblock_loop = block_ret;
							place_done = true;
							tmp = NULL;
							break;
						}
						else{
							if(Search_control_nodes(NULL,control_prev,tmp_null,tmp,NULL) && control_prev == controlnode)
								Create_subnodes_under_endnode(endnode,NULL,controlnode,block_ret,tmp_place,block_null,equalnode,NULL,tmpop,NULL,true,'p');
			
							else if(Search_control_nodes(NULL,control_prev,tmp_null,tmp,NULL)){
								if(!control_prev->bb_ptr) control_prev->bb_ptr = block_ret;
								else Insert_in_BasicBlock_list(control_prev,block_ret);
								//this var node should be showing the equal node which 
								if(!control_prev->control_out) control_prev->control_out = endnode;
								else tmp_null->equal_op_out = equalnode;
							}
							place_done = true;
							tmp = NULL;
							break;
						}
						if(!loop_start && tmp_control){
							if(!tmp_control->result_control) tmp_control->result_control = control_prev;
							else Insert_in_child_list(tmp_control->result_control,control_prev);
						}
						if(tmp_place->state_place_input){
							if(Search_var_from_statelist(tmp_place->state_place_input,tmpstate,false) && Search_state_from_controlnode_list(tmpstate,first_control_node,cntrl_empty)){
								if(!cntrl_empty->result_control) cntrl_empty->result_control = control_prev;
								else Insert_in_child_list(cntrl_empty->result_control,control_prev);
							}
						}
					}
					else {place_done = false; control_create = false;}
					tmp_place = tmp_place->next_place;
				}	
				//if(place_done) break;
	
			}
			
			else if(tmp->signal_selector_out && control_checkflag){
				//in this case, create a separate control body .firstcheck for the other state input signals to this signal selector and then create a control block
				if(tmp->signal_selector_out->state_in_signal){
					stateflag=true;
					tmpvar=tmp->signal_selector_out->state_in_signal;
					while(tmpvar){
						cntrl_empty = NULL;control_prev = NULL;
						if(Search_var_from_statelist(tmpvar,tmpstate,false) && Search_state_from_controlnode_list(tmpstate,first_control_node,control_prev)){
							
							if(tmpvar == tmp->signal_selector_out->state_in_signal){
								Create_control_node(control_new,control_prev->control_out,NULL,cntrl_empty,first_state,control_prev,tmp->signal_selector_out,NULL,NULL,false);
							
								control_create=true;
								if(!loop_start && tmp_control){
									if(!tmp_control->result_control) tmp_control->result_control = control_new;
									else Insert_in_child_list(tmp_control->result_control,control_new);
									//control_new->control_in = tmp_control;
									tmp_control->control_out->signal_selector_out = control_new->signal_select_node;	
								}
							}
							else if(control_prev){
								if(!control_prev->result_control) control_prev->result_control = control_new;
								else Insert_in_child_list(control_prev->result_control,control_new);
								//control_new->control_in = control_prev;
								//else Insert_in_child_list(control_new->control_in,control_prev);
							}
						}
						//no need of waiting for all states to be attached,even if their control blocks have not been created
						tmpvar=tmpvar->next_n;
					}
				}
				//if either no state
				if(!stateflag || (stateflag && !control_create)){
					tmpvar = tmp->signal_selector_out->in_signal_list;
					while(tmpvar){
						controlnode = NULL;endnode = NULL;cntrl_empty = NULL;
						//in this case, all the tmpvar which is not same as tmp, must be searched and connected to this control_new 
						if(tmpvar == tmp->signal_selector_out->in_signal_list){
							if(Search_end_node_BasicBlock(tmpvar,first_basic_block,endnode,controlnode,true,block_ret,false,NULL) || Search_control_nodes(NULL,cntrl_empty,endnode,tmpvar,NULL)){
								Create_control_node(control_new,endnode,NULL,controlnode,first_state,cntrl_empty,tmp->signal_selector_out,NULL,NULL,false);
								if(!loop_start && tmp_control){
									if(!tmp_control->result_control) tmp_control->result_control = control_new;
									else Insert_in_child_list(tmp_control->result_control,control_new);
									//control_new->control_in = tmp_control;	
								}
							}
						}
						else if(Search_end_node_BasicBlock(tmpvar,first_basic_block,endnode,controlnode,true,block_ret,false,NULL)){
							control_new->control_in_from_dfg = endnode;
							if(!endnode->signal_selector_out)
								endnode->signal_selector_out = control_new->signal_select_node;
							else insert_in_operator_list(endnode,NULL,control_new->signal_select_node,false,NULL,false);
						}
						//control_prev is control node from where same node as tmpvar is generated. endnode_cntrl is that node in DFG.this case if tmpvar is an output from control node in existing DFG
						else if(Search_control_nodes(NULL,control_prev,endnode_cntrl,tmpvar,NULL)){
							control_prev->result_control = control_new;
							//control_new->control_in = control_prev;
							endnode_cntrl->signal_selector_out = control_new->signal_select_node;
						}
						tmpvar = tmpvar->next_n;
					}
				}
				tmp = tmp->signal_selector_out->out_signal;
			}
			else if(tmp->comparator_out && control_checkflag){
				controlnode = NULL;endnode = NULL;cntrl_empty = NULL;
				if(tmp->comparator_out->state_condition && Search_state_from_controlnode_list(tmp->comparator_out->state_condition,first_control_node,control_prev)){
					stateflag = true;
					tmpvar = tmp->comparator_out->lhs_compare;
					if(Search_end_node_BasicBlock(tmpvar,first_basic_block,endnode,cntrl_empty,true,block_ret,false,NULL) || Search_control_nodes(NULL,cntrl_empty,endnode,tmpvar,NULL)){
						Create_control_node(control_new,endnode,tmp->comparator_out,cntrl_empty,first_state,control_prev,NULL,NULL,NULL,false);
						control_create=true;
			
						if(!loop_start && tmp_control){
							if(!tmp_control->result_control) tmp_control->result_control = control_new;
							else Insert_in_child_list(tmp_control->result_control,control_new);
							//control_new->control_in = tmp_control;
							if(!tmp_control->control_out->comparator_out) tmp_control->control_out->comparator_out = control_new->control_compare_node;		
							else Insert_in_compare_list(tmp_control->control_out->comparator_out,control_new->control_compare_node);
						}
					}
					else control_create = false;		
				}
		
				if(!stateflag || (stateflag && !control_create)){
				
					if(!stateflag)
						tmpvar = tmp->comparator_out->condition_value;
					else tmpvar = tmp->comparator_out->lhs_compare;
					while(tmpvar){
						controlnode = NULL;endnode = NULL;cntrl_empty = NULL;
						if(Search_end_node_BasicBlock(tmpvar,first_basic_block,endnode,controlnode,true,block_ret,false,NULL) ||Search_control_nodes(NULL,cntrl_empty,endnode,tmpvar,NULL)){
							if(done == false)
								Create_control_node(control_new,endnode,NULL,cntrl_empty,first_state,controlnode,tmp->signal_selector_out,NULL,NULL,false);
							else{
								control_new->control_in_from_dfg = endnode;
								endnode->comparator_out = control_new->control_compare_node;
							}
							if(!loop_start && tmp_control){
								if(!tmp_control->result_control) tmp_control->result_control = control_new;
								else Insert_in_child_list(tmp_control->result_control,control_new);
								//control_new->control_in = tmp_control;			
							}
							
						}
						else if(Search_control_nodes(NULL,control_prev,endnode_cntrl,tmpvar,NULL)){
							if(done == false)
								Create_control_node(control_new,endnode_cntrl,tmp->comparator_out,control_prev,first_state,controlnode,NULL,NULL,NULL,false);
							else{
								if(!control_prev->result_control)
									control_prev->result_control = control_new;
								else Insert_in_child_list(control_prev->result_control,control_new);
								//control_new->control_in = control_prev;	
								endnode_cntrl->comparator_out = control_new->control_compare_node;
							}
							
						}
						if(!stateflag && tmpvar == tmp->comparator_out->condition_value)
							tmpvar = tmp->comparator_out->lhs_compare;
						else tmpvar = NULL;
						done = true;
					}
					
				}
				tmp = tmp->comparator_out->value_out;
			}
			else tmp=NULL;
			if(!place_done && !control_create) break;
			
		}//endofwhile
		//do-while loop continuation condition
		if( control_out->compnode || control_out->signalnode || control_out->opnode){
			if(control_out->compnode){
				check = true;
				if(tmpout == control_out->compnode->value_out)
					flag = false;
				else tmpout = control_out->compnode->value_out;
		
			}
			if(control_out->signalnode){
				if(!flag)
					tmpout = control_out->signalnode->out_signal;
				else if(flag && !check){
					check = true;
					if(tmpout == control_out->signalnode->out_signal)
						flag = false;
					else tmpout = control_out->signalnode->out_signal;
				}
			
			}
			if(control_out->opnode){
				if(!flag)
					tmpout = control_out->opnode->output_value;
				else if(flag && !check){
					check = true;
					if(tmpout == control_out->opnode->output_value)
						tmpout = NULL;
					else
						tmpout = control_out->opnode->output_value;
				}
			}
	
		}	
		
		loop_start = true;
	}while(tmpout);	
		
}
if(control_out->dfgnode){
		//REFERENCE 3
	if(control_out->dfgnode->condition_op)
		//tmp = control_out->dfgnode->condition_op->if_cond_var;
		tmpcond = control_out->dfgnode->condition_op;
		while(tmpcond){
			endnode = NULL;control_prev = NULL;
			tmp = tmpcond->assign_expr->rhs_value;
			//if(!tmpcond->prev_cond)	
			//control_prev is the control block from where tmp is generated. it is returned from the below function. this case is for the if_cond_var only
				//Create_nodes_for_conditional_block(tmp , tmpcond,first_state,control_prev,control_new,block_ret);
			//else{
				//data_block not known because it is not known in which basic_block assign_expr->rhs_value will be found
				//control_prev here will contain the control_block where if_cond_var was generated
				
				Create_nodes_for_conditional_block(tmp,tmpcond,first_state,control_prev,control_new,block_ret);
				//if(!control_new->bb_ptr) control_new->bb_ptr = block_ret;
				//else Insert_in_BasicBlock_list(control_new,block_ret);
				//control_new->control_out = endnode;
				//control_new->control_out->equal_op_out = endnode->equal_op_out;
			//}
			control_prev = control_new;
			tmpcond = tmpcond->next_cond;
		}

	tmp = endnode->equal_op_out->lhs_value;
	//if(endnode)
	//	Create_subnodes_under_endnode(endnode,NULL,control_prev,block_ret,tmp_place,block_null,equalnode,NULL,tmpop,NULL,'p');
	//Insert_path_in_BasicBlock(control_prev,block_ret,tmpvar,first_state,endnode->equal_op_out->lhs_value,false);
}

return place_done;

}

//function to check if the path started by node_basicblock has been implemented in DFGgraph, and for matching, the same node in petri graph is also traversed for comparing.
//path flag is to indicate if the first node in the petrigraph path and the dfg path has been matched. if its false, then no need to proceed further
//this fn currently just checks for the next immediate node from node_basicblock if its created according to the path from node_petri. if you wish to check for further path comparsion, just uncomment the word "continue" and comment "break"
bool Check_creation_of_path(DeclareData *node_basicblock,DeclareData *node_petri,DeclareData*& result_endnode){

DeclareData *tmp_petri=NULL;
DeclareData *tmp_dfg=NULL;
DeclareData *tmp = NULL;
bool path= false;
bool search=false;

tmp_dfg = node_basicblock;
tmp_petri = node_petri;

while(tmp_dfg && tmp_petri){
	
	if(tmp_dfg->equal_op_out && (tmp_petri->place_ptr || tmp_petri->equal_op_out || tmp_petri->transition_out)){
		if(tmp_petri->place_ptr) tmp = tmp_petri->place_ptr->first_trans_node->data_node->condition_op->assign_expr->lhs_value;
		else if(tmp_petri->equal_op_out) tmp=tmp_petri->equal_op_out->lhs_value;
		else if(tmp_petri->transition_out) tmp = tmp_petri->transition_out->output_var;
		if(!strcmp(tmp_dfg->equal_op_out->lhs_value->name , tmp->name)){
			search = true;
			path=true;
			tmp_petri = tmp;
			 tmp_dfg = tmp_dfg->equal_op_out->lhs_value;
			// continue;
			break;
		}
		//if the first node in the path didnt match, then no need of proceeding further
		else if(!path){
			search = false;
			break;
		}
		else{
			search = true;
			result_endnode = tmp_dfg;
			break;
		}
		
	
	}
	else if(tmp_dfg->operator_out && tmp_petri->operator_out){
		tmp = tmp_petri->operator_out->output_value;
		if(!strcmp(tmp_dfg->operator_out->output_value->name,tmp->name)){
			search=true;
			path=true;
			tmp_petri = tmp;
			tmp_dfg = tmp_dfg->operator_out->output_value;
			continue;
		}
		else if(!path){
			search = false;
			break;
		}
		else{
			search=true;
			result_endnode=tmp_dfg;
			break;
		}
		
	}
	else tmp_dfg=NULL;
	
}

return search;


}

//function to search if comp,sig,dfg is there in control_compare n return true if yes
bool Search_in_list(Compare_operator *comp , Signal_selector *sig,DFG_block *dfg,Operate_op *oper,Path_list *control_compare){

bool search = false;

if(comp && control_compare->compnode == comp)
	search = true;
else if(sig && control_compare->signalnode == sig)
	search = true;
else if(dfg && control_compare->dfgnode == dfg)
	search = true;
else if(oper && control_compare->opnode == oper)
	search = true;	

return search;
}


//function to delete the loop_list
void delete_loop_list(void){

int i=0;
Path_list *tmp = NULL;
tmp = loop_list[0];

while(loop_list[i]){
	delete loop_list[i];
	loop_list[i]=NULL;
	i++;
}

}


//function to connect the already created loop_node(DFG) until the node which leads to control_result(petri)
//until this function is called control_result(controlnode_check) has not been implemented in DFG yet via exit_node
//headernode is the header of the loop
//since this fn connectsthe path between control_loop and controlnode_check, then the nodes between them can only be control nodes(eqnode or comp or signode or opnode(ONLY<sign) .cannot be placenode or opnode or trannode
//when this fn is called, the exit_node is the outgoing next node from a node in the loop_list, so the input of this exit_node must be first searched and then exit_nodes must be implemented
void Connect_control_loopto_controlnode_check(Control_block *loop_node,Path_list *control_result,Path_list *exit_node,Path_list *headernode){

//so iterate via exit_node first. 

Path_list *tmp = NULL;
DeclareData *endnode=NULL , *endnode_1 = NULL;
DeclareData *tmpvar = NULL ,*outvar = NULL;
Transition_block *tmptran = NULL;
Control_block *controlnode=NULL;
Basic_block *block_ret=NULL;
Compare_operator *tmpcomp=NULL;
Signal_selector *tmpsig = NULL;
Place_block *tmpplace = NULL;
Operate_op *tmpoper = NULL;
Equal_to_op *tmpeq=NULL;
Equal_to_op *eqnode = NULL;
Path_list *noderet = NULL;
DFG_block *tmpdfg = NULL;
bool loop = false;

//noderet not going to be used after this function below.its garbage variablr.destroy it after Search_header has been called
noderet = new Path_list;
Initialize_array_pointer(noderet);

tmp = exit_node;
while(tmp){
	loop = true;
	endnode = NULL;controlnode = NULL;
	//exit_node is the node just after the exitpoint of the loop,which isnt a part of the loop
	
	do{	
		endnode = NULL;controlnode = NULL;
		//create only node by node. cannot call Insert_pathinBasicBlock;
	//create the child node only n return here n check if the next node is one of controlnode_check
		if(!loop){
			tmpcomp = tmpvar->comparator_out;
			tmpoper = tmpvar->operator_out;
			tmpplace = tmpvar->place_ptr;
			tmptran = tmpvar->transition_out;
			tmpsig = tmpvar->signal_selector_out;
			tmpeq= tmpvar->equal_op_out;
			tmpdfg = tmpvar->dfgnode_out;
		}
		//firs time this will execute
		else{
			tmpcomp = tmp->compnode;
			tmpsig = tmp->signalnode;
			tmpeq = tmp->eqnode;
			tmpoper = tmp->opnode;
			tmpplace = tmp->placenode;
			tmptran = tmp->trannode;
		}
		/*
		if(tmpcomp || tmpsig){
			//here
			
			noderet->compnode = tmpcomp;
			noderet->signalnode = tmpsig;
			if(Trace_control_result(exit_node,noderet,first_state,loop_node,false)){
				//traceflag = true;
				if(noderet->compnode)
					tmpvar = noderet->compnode->value_out;
				else tmpvar = noderet->signalnode->out_signal;
				break;
			}
		}*/	
		if(tmpeq || tmpplace || tmptran){
			if(tmpeq)
				tmpvar = tmpeq->rhs_value;
			else if(tmpplace)
				tmpvar = tmpplace->first_trans_node->data_node->condition_op->assign_expr->rhs_value;
			else tmpvar = tmptran->data_node->assignment_graph->rhs_value;
			if(Search_control_nodes(NULL,controlnode,endnode,tmpvar,NULL)){
				eqnode = new Equal_to_op;
				Initialize_structures(NULL,NULL,NULL,NULL,eqnode,NULL);
				if(!endnode->equal_op_out) endnode->equal_op_out = eqnode;
				else Insert_in_equalto_list(NULL,endnode,eqnode);
				eqnode->rhs_value = endnode;
				eqnode->lhs_value = new DeclareData;
				if(tmpeq)
					assign_value(eqnode->lhs_value,tmpeq->lhs_value);
				else if(tmpplace)
					assign_value(eqnode->lhs_value,tmpplace->first_trans_node->output_var);
				else assign_value(eqnode->lhs_value,tmptran->output_var);
				
				if(tmpeq)
					tmpvar = tmpeq->lhs_value;
				else if(tmpplace)
					tmpvar = tmpplace->first_trans_node->output_var;
				else tmpvar = tmptran->output_var;
			}
			else break;
			
		}
		else if(tmpoper && (tmpoper->op_type!= '<')){

			if((tmpoper->op1->data_type!=integer && Search_control_nodes(NULL,controlnode,endnode,tmpoper->op1,NULL)) || (tmpoper->op2->data_type!=integer && Search_control_nodes(NULL,controlnode,endnode_1,tmpoper->op2,NULL))){
				if(endnode){
					endnode->operator_out = new Operate_op;
					Initialize_structures(NULL,NULL,NULL,endnode->operator_out,NULL,NULL);
					endnode->operator_out->op1 = endnode;
				}
				else{
					endnode_1->operator_out = new Operate_op;
					Initialize_structures(NULL,NULL,NULL,endnode_1->operator_out,NULL,NULL);
					endnode_1->operator_out->op2 = endnode_1;
				}
				tmpvar = tmpoper->output_value;
			}
		}
		else tmpvar = NULL;
		
		if(tmpcomp && Search_in_list(tmpcomp,NULL,NULL,NULL,control_result))
			break;
		else if(tmpsig && Search_in_list(NULL,tmpsig,NULL,NULL,control_result))
			break;
		else if(tmpdfg && Search_in_list(NULL,NULL,tmpdfg,NULL,control_result))
			break;
		else if(tmpoper && tmpoper->op_type== '<' && Search_in_list(NULL,NULL,NULL,tmpoper,control_result))
			break;
		
		loop = false;
	}while(tmpvar);
	
	tmp = tmp->next_node;
	

}//end of while

delete noderet;
noderet = NULL;


}


void Delete_looplist_nodes(void){
	
int i=0;
while(loop_list[i]){
	if(!loop_list[i]->varnode && !loop_list[i]->placenode && !loop_list[i]->trannode && !loop_list[i]->eqnode && !loop_list[i]->opnode && !loop_list[i]->compnode && !loop_list[i]->signalnode && !loop_list[i]->dfgnode){
		delete loop_list[i];
		loop_list[i] = NULL;
	}
	i++;
}
	
}


//fn to search varsearch as output of anynode from the loop_list, if found , chedk if the output is from a placenode. if not trace backwards until you get a place and send it back
bool Search_output_of_LoopList(DeclareData *varsearch , Place_block*& place_ret){

int i=0;
bool search = false;
DeclareData *tmp = NULL;

while(loop_list[i]){
	if(loop_list[i]->placenode && !strcmp(varsearch->name,loop_list[i]->placenode->first_trans_node->output_var->name)){
		place_ret = loop_list[i]->placenode;
		search = true;
		break;
	}
	/*
	else if(loop_list[i]->varnode && loop_list[i]->varnode && !strcmp(varsearch->name,loop_list[i]->varnode->name)){
	//	varfound = loop_list[i]->varnode;
		if(Search_output_of_LoopList(loop_list[i]->varnode,place_ret)){
			search = true;
			break;
		}
	}*/
	else if(loop_list[i]->trannode && !strcmp(varsearch->name,loop_list[i]->trannode->output_var->name)){
		//varfound = loop_list[i]->trannode->output_var;
		if(Search_output_of_LoopList(loop_list[i]->trannode->data_node->assignment_graph->rhs_value,place_ret)){
			search = true;
			break;
		}
	}
	else if(loop_list[i]->opnode && !strcmp(varsearch->name , loop_list[i]->opnode->output_value->name)){
		tmp = loop_list[i]->opnode->op1;
		do{
			if(tmp->data_type!= integer && Search_output_of_LoopList(tmp,place_ret)){
				search = true;
				break;
			}
			
			if(tmp == loop_list[i]->opnode->op1)
				tmp = loop_list[i]->opnode->op2;
			else tmp = NULL;
		
		}while(tmp);
	}
	else if(loop_list[i]->eqnode && !strcmp(varsearch->name , loop_list[i]->eqnode->lhs_value->name)){
		if(Search_output_of_LoopList(loop_list[i]->eqnode->rhs_value,place_ret)){
			search = true;
			break;
		}
	}
	
	if(search) break;
	i++;
}

return search;

}



//both DFG or Petrinet

//function to check the entire petri- net model for possible loops n follow same  as analysis_parse
//this function should first check if there is a loop. If yes, check further if the header of the loop, is connected to a node like comparator,or a signal selector,which is not part of the loop
//start flag is to indicate if the dataflow/controlflow loop has been found.
//loop_done flag is to indicate if the loop has been created and its exit path also has been traced and implemented
//for dataflow loops, the exit_nodes will be rturned via this function to where the fn has been called, and their paths will be created there itself.

//searchflag is to indicate to search a variable in the loop, and send it back through this function
bool Check_loop_body(DeclareData *varsearch , State_var *first_state,bool& loop_done,bool& dataflow,Path_list*& exit_node,bool search_dfg,DeclareData*& first_node,Control_block*& control_loop,bool create_loop, Path_list*& header_node,bool searchflag,Place_block*& place_search,DeclareData *var_find,Control_block *control_st){

int i=0,num=0;
bool start=false;
bool control_flow = false , statecheck = false,placecheck = false , flag = false, opcreate = true;
bool checkstate=false;
bool node_down=false;
bool no_state=false;
bool startloop=false;
bool loop_type=false;
Basic_block *block_ret = NULL;
Basic_block *basicblock_loop = NULL;
Basic_block *blocknull = NULL;
Control_block *control_attach=NULL;
Control_block *controlnode = NULL , *control_ret = NULL , *tmp_control = NULL, *controlnode_tmp = NULL;
State_var *tmpstate=NULL;
DeclareData *tmpinput=NULL;
DeclareData *endnode=NULL , *endnode_tmp = NULL , *tmpvar = NULL, *temp = NULL , *tmp_prev = NULL , *prev_var = NULL;
DeclareData *node_empty = NULL;
Compare_operator *prev_comp = NULL;
Signal_selector *prev_signal = NULL;
Path_list *tmpnode=NULL;
Path_list *tmp_exit=NULL;
Path_list *loop_node=NULL , *first_loopnode = NULL, *startnode = NULL , *nextnode = NULL;
Path_list *controlnode_check=NULL;
Place_block *tmp_place = NULL;
Equal_to_op *equalnode=NULL, *tmpeq = NULL, *eq_temp = NULL;
Operate_op *tmpop=NULL , *prevop = NULL;
Condition_block *tmpcond = NULL;
DeclareData *var_list[10];
State_var *tmpstate_list[10];

if(Search_back_petri_model(varsearch,NULL,true,true,first_state,i,false,loop_node,false,var_list,10,search_dfg,block_ret,false,endnode)){

	//to check if the looop already exists in DFG EDITING HERE
	if(!search_dfg && Search_node_in_DataLoop(varsearch,varsearch,endnode,true,first_basic_block,tmp_exit))
		create_loop = false;
	
	
	for(i=0;i<10;i++){
		loop_list[i] = new Path_list;
		Initialize_array_pointer(loop_list[i]);
	}
	i=0;
	loop_list[i++]->varnode = varsearch;
		
	start = Search_back_petri_model(varsearch,NULL,true,false,first_state,i,false,loop_node,false,var_list,10,search_dfg,block_ret,false,endnode); //endnode is null here

}

//now create the path of nodes which form the loop
if(start){
	endnode = NULL;
	
	if(searchflag){
		//Check for output of nodes in loop_list to search for varsearch
		if(!search_dfg && Search_output_of_LoopList(var_find,place_search))
			create_loop = false;
		else if(search_dfg && Search_loop_for_node(10,var_find,first_node))
			create_loop = false;
	}
	
	//here it should be decided if the header of the loop is connected to a comparator or signal selector or DFG. For this, the header must be detected and traced depthwise.
	loop_type = Search_Header_of_loop(first_state,header_node,search_dfg);
	Delete_looplist_nodes();
	// ALGORITHM 2 called here: if header is found, then search for the edge of the header away from the loop if its connected to comparator or signal selector or DFG(even if not immediately connected, must be searched depthwise for comparator or SS).
	//first check if header is the exit point of loop, if yes, trace depthwise to search for comparator, else check other nodes of the loop if its indirectly connected to comp or SS or DFG
	if(loop_type){
		//controlnode_check is the node containing the comp/SS/dfg
		if(Check_exitpoint_of_loop(header_node,NULL,NULL,exit_node,controlnode_check,true,true))
			control_flow = true;
		else{
			control_flow = false;
			dataflow = Check_exitpoint_of_loop(header_node,NULL,NULL,exit_node,controlnode_check,false,true);
			//here exit_node contains the set of start nodes of the path away from the dataflow loop
			//if the loop is to be created, then assign the basicblock of the control_st to basicblock_loop
			if(control_st && create_loop){
				if(!control_st->bb_ptr){
					control_st->bb_ptr = new Basic_block;
					Initialize_nodes(NULL,NULL,NULL,NULL,control_st->bb_ptr,NULL);
					Insert_in_BasicBlock_list(NULL,control_st->bb_ptr);
					basicblock_loop = control_st->bb_ptr;
				}
				basicblock_loop = control_st->bb_ptr;
			}
		}
	}
	else{
		//if no header is found it must be declared as control flow loop. hence must find exit point of the loop.
		
		//first implement the control loop STEP 1 DONE
		if(create_loop)
			Create_control_loop_block(control_loop,header_node);
		control_flow = true;
			//by sending true, controlnode_check has the comp/SS/DFG
			//STEP 2
			//this function already sends the controlnode_check which contains the comp/SS/dfg the controlloop is connected to
		if(Check_exitpoint_of_loop(header_node,NULL,NULL,exit_node,controlnode_check,true,true)){
		//exit_node can be more than one (petrigraph)
		
		//first,connect the control_loop until the controlnode_check(petrigraph)
		//this function will create the path in DFG from tmp_exit(petri) to controlnode_check(petri)
			if(create_loop){
				Connect_control_loopto_controlnode_check(control_loop,controlnode_check,exit_node,header_node);
					//now trace controlnode_check,and create the controlnodes and check if the dataflow nodes controlled by the output of this node is created or not in DFG. 
				if(Trace_control_result(NULL,controlnode_check,first_state,control_loop,true,basicblock_loop)){
					loop_done = true;
					if(basicblock_loop) control_loop->bb_ptr = basicblock_loop;
				}
				else{
					control_loop->bb_ptr = new Basic_block;
					Initialize_nodes(NULL,NULL,NULL,NULL,control_loop->bb_ptr,NULL);
					Insert_in_BasicBlock_list(NULL,control_loop->bb_ptr);
					loop_done = true;
				}
				if(Search_back_loop(NULL,control_loop->control_dfg_node,varsearch,endnode))
					first_node = endnode;
					
				delete_loop_list();
			}
		}	
		//}
	}
	i=num;
	
	//this is creating the loop in basic_block if the loop detectd is a dataflow loop
	//here we assume that the dataflow loop nodes are all active in atleast one common state( CURRENT ASSUMPTION)
	if(!control_flow && dataflow && create_loop){
		
		
		first_loopnode = new Path_list;
		Initialize_array_pointer(first_loopnode);
		Search_header_in_looplist(header_node,startnode,nextnode,false,i);
		num=i; // here the index of the loop_list node whose output is varsearch is stored
		startloop = true;
		do{
			if(startloop)
				//search for the loop_list node which is the header_node(startnode) and return the index "i" of the node next to it ,tmpnode= null
				Search_header_in_looplist(startnode,tmpnode,nextnode,true,i);
			else 
				i++;
			
			tmpeq = NULL; tmpop = NULL; opcreate = true;
			if(loop_list[i] && loop_list[i]->placenode){
				tmp_place = loop_list[i]->placenode;
				if(tmp_place->state_place_input){
					tmpvar = tmp_place->state_place_input;
					while(tmpvar){
						if(Search_var_from_statelist(tmpvar,tmpstate,false) && Search_state_from_controlnode_list(tmpstate,first_control_node,control_ret)){
							statecheck = true;
							break;
						}
						tmpvar = tmpvar->next_n;
					}
				}
					//pass control_st to this function
				
					if(!statecheck && !tmp_place->state_place_input){
						tmpvar = tmp_place->first_place_input;
						if(tmp_place->first_trans_node->data_node->assignment_graph){
							temp = tmp_place->first_trans_node->data_node->assignment_graph->rhs_value;
							tmpeq = tmp_place->first_trans_node->data_node->assignment_graph;
						}
						else{
							 temp = tmp_place->first_trans_node->data_node->condition_op->assign_expr->rhs_value;
							 tmpeq = tmp_place->first_trans_node->data_node->condition_op->assign_expr;
							 if(tmp_place->first_trans_node->data_node->condition_op->equal_cond)
							 	eq_temp = tmp_place->first_trans_node->data_node->condition_op->equal_cond;
						}
						while(tmpvar){
							if(strcmp(tmpvar->name , temp->name)){
								if(tmpvar->unary_operator || Search_var_from_graph(tmpvar,NULL,NULL,prev_comp,prev_signal,prevop,node_empty,first_state,false,true)){
									if(Search_control_nodes(NULL, controlnode ,node_empty, tmpvar,NULL)){
										prev_var = node_empty;
									//	if(prev_comp)
									//		Create_control_node(tmp_control,endnode,prev_comp,control_st,first_state,controlnode,NULL,NULL,tmpeq,true);
									//	else if(prev_signal)
										//	Create_control_node(tmp_control,endnode,NULL,control_st,first_state,controlnode,prev_signal,NULL,tmpeq,true);
										// if(prevop)
											tmp_control = controlnode;
										placecheck = true;
									}
									else placecheck = false;
								}
							}
							else if(eq_temp && !strcmp(tmpvar->name,eq_temp->lhs_value->name) && Search_end_node_BasicBlock(tmpvar,first_basic_block ,endnode_tmp,controlnode_tmp,true, block_ret,false,NULL)){
								Create_control_node(tmp_control,endnode_tmp,NULL,control_st,first_state,controlnode_tmp,NULL,tmp_place->first_trans_node->data_node->condition_op,NULL,false);
								placecheck = true;
								break;
							}
							
							 tmpvar = tmpvar->next_n;
						}
					}
					if(!startloop){
						endnode = tmp_prev;
						if(statecheck)
							controlnode = control_ret;
						else if(placecheck)
							controlnode = tmp_control;
						
					}			
					else if(startloop && Search_end_node_BasicBlock(varsearch , first_basic_block ,endnode,controlnode,true, block_ret,false,NULL))
						controlnode = control_st;
						
					tmpeq = NULL;
					//check if output of tmp_place is already in the DFG graph 	EDITING HERE - 
					if(Search_end_node_BasicBlock(tmp_place->first_trans_node->output_var,first_basic_block,endnode_tmp,controlnode_tmp,true,block_ret,false,NULL)){
						opcreate = false; //output of tmp_place is already created (endnode_tmp)
						Create_subnodes_under_endnode(endnode ,NULL,controlnode,basicblock_loop,tmp_place,blocknull,tmpeq,NULL,tmpop,NULL,false, 'p');
						//here dont create the output of the tmpeq and attach endnode_tmp to the tmpeq
						tmpeq->lhs_value = endnode_tmp;
					}
					else if(opcreate)
						Create_subnodes_under_endnode(endnode ,NULL,controlnode,basicblock_loop,tmp_place,blocknull,tmpeq,NULL,tmpop,NULL,true, 'p');
					
					tmp_prev = tmpeq->lhs_value;	
					
					if(prev_var) 
						prev_var->equal_op_out = tmpeq;					//node_down = true;
					if(tmp_control){
						if( !tmp_control->bb_ptr) tmp_control->bb_ptr = basicblock_loop;
						Insert_in_BasicBlock_array(basicblock_loop,10,tmp_control);
					}
					else if(control_ret)  //control_ret is a state control node
						Insert_in_BasicBlock_array(basicblock_loop,10,control_ret);
						
					if(startloop) flag = true;
						
			//check for the state input if its there ,and if yes, then search from control list and attach it to the 
			}
			else if(loop_list[i] && loop_list[i]->eqnode){
				if(!startloop){
					endnode = tmp_prev;
					if(control_loop) controlnode = control_loop;
					else controlnode = NULL;
					
				}
				//occurs only one time
				else if(startloop && Search_end_node_BasicBlock(varsearch,first_basic_block,endnode,controlnode,true,block_ret,false,NULL))
					controlnode = control_st;
					
					
				tmpeq = NULL;
				Create_subnodes_under_endnode(endnode,NULL,controlnode,basicblock_loop,NULL,blocknull,tmpeq,loop_list[i]->eqnode,tmpop,NULL,true,'b');
				tmp_prev = tmpeq->lhs_value;
				if(startloop) flag = true;
			}
			else if(loop_list[i] && loop_list[i]->trannode){
				if(!startloop){
					endnode = tmp_prev;
					if(control_loop) controlnode = control_loop; //control_st remains the same
					else controlnode = NULL;
					
				}
				else if(startloop && Search_end_node_BasicBlock(varsearch,first_basic_block,endnode,controlnode,true,block_ret,false,NULL))
					controlnode = control_st;
				
					
				equalnode = loop_list[i]->trannode->data_node->assignment_graph;
				tmpeq = NULL;
				Create_subnodes_under_endnode(endnode,NULL,controlnode,basicblock_loop,NULL,blocknull,tmpeq,equalnode,tmpop,NULL,true,'t');
				tmp_prev = tmpeq->lhs_value;
				if(startloop) flag = true;
			}
			else if(loop_list[i] && loop_list[i]->opnode){
				//check forthe input which is not part of the loop.
				tmpop = NULL;
				if(!startloop){
					endnode = tmp_prev;
					if(control_loop) controlnode = control_loop;
					else controlnode = NULL;
					
				}
				else if(startloop && Search_end_node_BasicBlock(varsearch,first_basic_block,endnode,controlnode,true,block_ret,false,NULL))
					controlnode = control_st;
				
					
				tmpvar = loop_list[i]->opnode->op1;
				//search for the other input- tmpvar
				//temp stores the equivalent of endnode
				while(tmpvar){
					if(!strcmp(endnode->name, tmpvar->name)){
						temp = tmpvar;
						continue;
					}
					else break;
					if(tmpvar == loop_list[i]->opnode->op1)
						tmpvar = loop_list[i]->opnode->op2;
					else tmpvar = NULL;
				}
				if(tmpvar && Search_end_node_BasicBlock(tmpvar,first_basic_block,endnode_tmp,controlnode_tmp,true,blocknull,false,NULL)){
					//here blocknull contains the basicblock which contains tmpvar
					//check if the operator is connected from endnode_tmp
					if(endnode_tmp->operator_out){
						opcreate = false;
						endnode->operator_out = endnode_tmp->operator_out;
						tmpop = endnode_tmp->operator_out;
						if(endnode_tmp->operator_out->op1)
							endnode_tmp->operator_out->op2 = endnode;
						else endnode_tmp->operator_out->op1 = endnode;
					}
					//else store the other input in endnode_tmp itself
				}
				else opcreate = true;
					//if both tmpvar and varsearch are in same block, then no need to send thru blocknull
				if(basicblock_loop == blocknull)
					blocknull = NULL;
				//else blocknull will have the block which has tmpvar       temp has the petrigraph equivalent of endnode
				if(opcreate)
					Create_subnodes_under_endnode(endnode,temp,controlnode,basicblock_loop,NULL,blocknull,tmpeq,NULL,tmpop,loop_list[i]->opnode,false,'a');
				tmp_prev = tmpop->output_value;
				
				if(startloop) flag = true;
					
			}
			if(flag){
				//i = 9;
				startloop = false;
				flag = false;
			}
			if(i==9)
				i=0;
			if(i==num){
				if(tmpeq) first_loopnode->eqnode = tmpeq;
				else if(tmpop) first_loopnode->opnode = tmpop;
			}
			
		}while(i<10 && strcmp(tmp_prev->name,varsearch->name));
		

		//Attach_first_node_in_Loop(tmp_prev , first_loopnode);
		delete first_loopnode;
		first_loopnode = NULL;

		//Do not delete the loop_list now. Delete at the end of the main function
		//if(!flag)
		//	delete_loop_list();
	
	}
	else if(control_flow && !control_loop && create_loop){
		//in this part, the loop will be created as a control block. This part is for building the control loop having a header
		//check if the control_loop->control_out has been initialized
		Create_control_loop_block(control_loop,header_node);
		if(Check_exitpoint_of_loop(header_node,NULL,NULL,exit_node,controlnode_check,true,true)){
			Connect_control_loopto_controlnode_check(control_loop,controlnode_check,exit_node,header_node);
			if(Trace_control_result(NULL,controlnode_check,first_state,control_loop,true,basicblock_loop))
				loop_done = true;
				
			delete_loop_list();
		}
			
	}
	else delete_loop_list();
	
}

return start;
}





//function to create the control loop block, loop_list in DFG graph
//header_node may or may not be present. If header_node present, start implementing from header_node.
//ALGORIRTHM 4

//for storing the placenodes, you must store it in separate variable-placenode. the state and place control inputs must be resolved and attached to this loop_block before proceeding. 
//NOTE : // in this case, either we have found the node which leads to varnode or the first node in loop_list is a varnode
//now create startnode with no input/rhs_value and only create the lhs_value/output for now.
//startnode will be the header_node if header_node exists
void Create_control_loop_block(Control_block*& loop_block,Path_list *header_node){


DFG_block *tmpdfg = NULL;

Path_list *tmpnode=NULL;
Path_list *startnode=NULL;
Equal_to_op *eqnode=NULL;
Operate_op *oper=NULL;
State_var *tmpstate=NULL;
DeclareData *tmpvar=NULL;
Control_block *control_ret=NULL;
DeclareData *endnode = NULL;
Compare_operator *comp=NULL;
Place_block *placenode = NULL;
int i;
bool startflag=false;
bool check = false;
bool leftinput=false;
DeclareData *A_petri=NULL;


//first create the control block which will hold this loop. This control block should be in the control_list if there is no header_node

loop_block = new Control_block;
Initialize_nodes(NULL,NULL,NULL,loop_block,NULL,NULL);
if(!header_node)
	Insert_in_control_list(first_control_node,loop_block);

loop_block->control_dfg_node = new DFG_block;
Initialize_structures(NULL,loop_block->control_dfg_node,NULL,NULL,NULL,NULL);

if(header_node)
	startnode = header_node;

else if(loop_list[0]->varnode){
	//search for the node in loop_list which has input as varnode
	tmpvar = loop_list[0]->varnode;
	i=1;
	tmpnode = loop_list[i];
	while(tmpnode){
		if(tmpnode->placenode && tmpvar == tmpnode->placenode->first_trans_node->output_var)
			startnode = tmpnode;
		else if(tmpnode->trannode && tmpvar == tmpnode->trannode->output_var)
			startnode = tmpnode;
		else if(tmpnode->opnode && tmpvar == tmpnode->opnode->output_value)
			startnode = tmpnode;
		else if(tmpnode->compnode && tmpvar == tmpnode->compnode->value_out) 
			startnode = tmpnode;
		else if(tmpnode->eqnode && tmpvar == tmpnode->eqnode->lhs_value)
			startnode = tmpnode;
			
		if(startnode) break;
		tmpnode = loop_list[++i];
	}
	//if(startnode)
	//	startflag = true;
}

//refer to NOTE
if(startnode  || !loop_list[0]->varnode){

	if(!startnode && !loop_list[0]->varnode)
		startnode = loop_list[0];

	if(startnode->placenode)
		placenode = startnode->placenode;
	else if(startnode->trannode)
		eqnode = startnode->trannode->data_node->assignment_graph;
	else if(startnode->eqnode)
		eqnode = startnode->eqnode;
	else if(startnode->opnode)
		oper = startnode->opnode;
	else if(startnode->compnode)
		comp = startnode->compnode;
		
		//A_petri is the varnode used to store the inputvalue of the startnode(petrigraph)
	if(eqnode || placenode){
		loop_block->control_dfg_node->assignment_graph = new Equal_to_op;
		Initialize_structures(NULL,NULL,NULL,NULL,loop_block->control_dfg_node->assignment_graph ,NULL);
		loop_block->control_dfg_node->assignment_graph->lhs_value = new DeclareData;
		if(eqnode)
			assign_value(loop_block->control_dfg_node->assignment_graph->lhs_value,eqnode->lhs_value);
		else if(placenode) 
			assign_value(loop_block->control_dfg_node->assignment_graph->lhs_value,placenode->first_trans_node->output_var);
		if(eqnode) A_petri = eqnode->rhs_value;
		else A_petri = placenode->first_trans_node->data_node->assignment_graph->rhs_value;
		
		if(placenode){
			if(placenode->state_place_input){
				tmpvar = placenode->state_place_input;
				while(tmpvar){
					if(Search_var_from_statelist(tmpvar,tmpstate,false) && Search_state_from_controlnode_list(tmpstate,control_ret,first_control_node)){
						if(!control_ret->result_control) control_ret->result_control= loop_block;
						else Insert_in_control_list(control_ret->result_control,loop_block);
					}
					tmpvar = tmpvar->next_n;
				}
			}
			tmpvar = placenode->first_place_input;
			while(tmpvar){
				if(strcmp(tmpvar->name,placenode->first_trans_node->data_node->assignment_graph->rhs_value->name) && Search_control_nodes(NULL,control_ret,endnode,tmpvar,NULL)){
					if(!control_ret->result_control) control_ret->result_control= loop_block;
					else Insert_in_control_list(control_ret->result_control,loop_block);
				}
				tmpvar = tmpvar->next_n;
			}
		}
		//rhsvalue of dfggraph node will be created later
	}
	else if(oper){
		loop_block->control_dfg_node->operation_graph = new Operate_op;
		Initialize_structures(NULL,NULL,NULL,loop_block->control_dfg_node->operation_graph ,NULL,NULL);
		loop_block->control_dfg_node->operation_graph->output_value = new DeclareData;
		assign_value(loop_block->control_dfg_node->operation_graph->output_value,oper->output_value);
		if(oper->op1->data_type == integer){
			loop_block->control_dfg_node->operation_graph->op1 = new DeclareData;
			assign_value(loop_block->control_dfg_node->operation_graph->op1, oper->op1);
			A_petri = oper->op1;
		}
		else if(oper->op2->data_type == integer){
			loop_block->control_dfg_node->operation_graph->op2 = new DeclareData;
			assign_value(loop_block->control_dfg_node->operation_graph->op2,oper->op2);
			A_petri = oper->op2;
		}
	}
	i=1;
	tmpnode = loop_list[i];
	//store the output of the controlloop->dfgnode->output
	Create_loop_body_control_subfunction(loop_block,tmpnode,tmpvar,A_petri,i);
		
}
	
}




//this fn is created as sub-part of the Create_Control_loop_block() ,for creating the loop recursively.
void Create_loop_body_control_subfunction(Control_block*& loop_block,Path_list *tmpnode,DeclareData*& tmpvar,DeclareData *A_petri,int i){

bool check = false;
bool leftinput = false;
bool start = true;
//DeclareData *tmpvar =NULL;
DeclareData *tmp=NULL;
DeclareData *endnode=NULL;
State_var *tmpstate=NULL;
Control_block *control_ret=NULL;
Place_block *placenode = NULL;
Equal_to_op *eqnode = NULL;
Operate_op *oper = NULL;
Compare_operator *comp = NULL;
//DeclareData *A_petri=NULL;
DeclareData *firstvar = NULL;
Basic_block *block_ret=NULL;

firstvar = tmpvar;
if(loop_block->control_dfg_node->operation_graph)
		tmpvar = loop_block->control_dfg_node->operation_graph->output_value;
		
	else if(loop_block->control_dfg_node->assignment_graph)
		tmpvar =loop_block->control_dfg_node->assignment_graph->lhs_value;
		
	do{
		//Search for the tmpvar in the loop_list
		eqnode = NULL;placenode = NULL;oper = NULL;check = false;
		if(tmpnode->placenode){
			if((tmpnode->placenode->first_trans_node->data_node->assignment_graph && !strcmp(tmpvar->name,tmpnode->placenode->first_trans_node->data_node->assignment_graph->rhs_value->name)) || (tmpnode->placenode->first_trans_node->data_node->condition_op && !strcmp(tmpvar->name,tmpnode->placenode->first_trans_node->data_node->condition_op->assign_expr->rhs_value->name))){
				check = true;
				placenode = tmpnode->placenode;
			}
		}
		else if(tmpnode->trannode && !strcmp(tmpvar->name,tmpnode->trannode->data_node->assignment_graph->rhs_value->name)){
			check = true;
			eqnode = tmpnode->trannode->data_node->assignment_graph;
		}
		else if(tmpnode->eqnode && !strcmp(tmpvar->name , tmpnode->eqnode->rhs_value->name)){
			check = true;
			eqnode = tmpnode->eqnode;
		}
		else if(tmpnode->opnode){
			if(tmpnode->opnode->op1->data_type!=integer && !strcmp(tmpvar->name , tmpnode->opnode->op1->name)){
				check = true;
				leftinput = true;
				oper = tmpnode->opnode;
			}
			else if(tmpnode->opnode->op2->data_type!=integer && !strcmp(tmpvar->name , tmpnode->opnode->op2->name)){
				check = true;
				leftinput = false;
				oper = tmpnode->opnode;
			}
			else check = false;
		}
		else if(tmpnode->compnode && !strcmp(tmpvar->name , tmpnode->compnode->lhs_compare->name)){
			check=true;
			comp = tmpnode->compnode;
		}
		//creation of the nodes for dfggraph
		if(check){
				if(eqnode || placenode){
					if(!start && !strcmp(tmpvar->name,firstvar->name)){
						loop_block->control_dfg_node->assignment_graph->rhs_value = tmpvar;
						tmpvar->equal_op_out = loop_block->control_dfg_node->assignment_graph;
						tmpvar->equal_op_out->rhs_value = tmpvar;
					}
					else{
						tmpvar->equal_op_out = new Equal_to_op;
						Initialize_structures(NULL,NULL,NULL,NULL,tmpvar->equal_op_out,NULL);
						tmpvar->equal_op_out->rhs_value = tmpvar;
						tmpvar->equal_op_out->lhs_value = new DeclareData;
					}
					start = false;
					if(eqnode)
						assign_value(tmpvar->equal_op_out->lhs_value , eqnode->lhs_value);
					else assign_value(tmpvar->equal_op_out->lhs_value,placenode->first_trans_node->output_var);
						if(placenode){
							tmp = placenode->state_place_input;
							while(tmp){
								if(Search_var_from_statelist(tmp,tmpstate,false) && Search_state_from_controlnode_list(tmpstate,control_ret,first_control_node)){
									if(!control_ret->result_control) control_ret->result_control= loop_block;
									else Insert_in_control_list(control_ret->result_control,loop_block);
								}	
								tmp = tmp->next_n;
							}
							tmp = placenode->first_place_input;
							while(tmp){
								if(strcmp(tmp->name,placenode->first_trans_node->data_node->condition_op->assign_expr->rhs_value->name) && Search_control_nodes(NULL,control_ret,endnode,tmp,NULL)){	
									if(!control_ret->result_control) control_ret->result_control= loop_block;
									else Insert_in_control_list(control_ret->result_control,loop_block);
									endnode->equal_op_out = tmpvar->equal_op_out;
								}
								tmp = tmp->next_n;
							}
							
						}
					
					if(!strcmp(tmpvar->equal_op_out->lhs_value->name, A_petri->name)){
						if(loop_block->control_dfg_node->assignment_graph){
							loop_block->control_dfg_node->assignment_graph->rhs_value = tmpvar->equal_op_out->lhs_value;
							tmpvar->equal_op_out->lhs_value->equal_op_out = loop_block->control_dfg_node->assignment_graph;
							//tmpvar->equal_op_out->rhs_value = tmpvar;
						}
						else if(loop_block->control_dfg_node->operation_graph && leftinput){
							if(!loop_block->control_dfg_node->operation_graph->op1)
								loop_block->control_dfg_node->operation_graph->op1 = tmpvar->equal_op_out->lhs_value;
							 else loop_block->control_dfg_node->operation_graph->op2 = tmpvar->equal_op_out->lhs_value;
							 tmpvar->equal_op_out->lhs_value->operator_out = loop_block->control_dfg_node->operation_graph;
							 
						}
						//in  this case, the control loop has been entirely implemented, thus must break from the loop
						//break;					
					}
					else tmpvar = tmpvar->equal_op_out->lhs_value;
					
				}
				else if(oper){
					tmpvar->operator_out = new Operate_op;
					Initialize_structures(NULL,NULL,NULL,tmpvar->operator_out,NULL,NULL);
					if(oper->op1->data_type!=integer){
						tmpvar->operator_out->op1 = tmpvar;
						tmpvar->operator_out->op2 = new DeclareData;
						assign_value(tmpvar->operator_out->op2, oper->op2);
					}
					else{
						 tmpvar->operator_out->op2 = tmpvar;
						 tmpvar->operator_out->op1 = new DeclareData;
						 assign_value(tmpvar->operator_out->op1,oper->op1);
					}
					tmpvar->operator_out->output_value = new DeclareData;
					assign_value(tmpvar->operator_out->output_value , oper->output_value);
					
					if(!strcmp(tmpvar->operator_out->output_value->name,A_petri->name)){
						if(loop_block->control_dfg_node->assignment_graph)
							loop_block->control_dfg_node->assignment_graph->rhs_value = tmpvar->operator_out->output_value;
							
						else if(loop_block->control_dfg_node->operation_graph && leftinput)
							loop_block->control_dfg_node->operation_graph->op1 = tmpvar->operator_out->output_value;
							
						else 	loop_block->control_dfg_node->operation_graph->op2 = tmpvar->operator_out->output_value;
						
						break;
					}
					else tmpvar = tmpvar->operator_out->output_value;
				}
				//here we are assuming that the comp node is just a part of the control loop
				else if(comp){
					tmpvar->comparator_out = new Compare_operator;
					Initialize_nodes(NULL,tmpvar->comparator_out,NULL,NULL,NULL,NULL);
					tmpvar->comparator_out->lhs_compare = tmpvar;
					
					if(comp->state_condition && Search_state_from_controlnode_list(comp->state_condition,control_ret,first_control_node)){
						
						if(!control_ret->result_control) control_ret->result_control= loop_block;
						else Insert_in_control_list(control_ret->result_control,loop_block);
						if(!loop_block->control_in) loop_block->control_in = control_ret;
						else Insert_in_control_list(loop_block->control_in,control_ret);
					}
					if(comp->condition_value){
						if(Search_end_node_BasicBlock(comp->condition_value,first_basic_block,endnode,control_ret,true,block_ret,false,NULL)){
							loop_block->control_in_from_dfg = endnode;
							tmpvar->comparator_out->condition_value = endnode;
							endnode->comparator_out = tmpvar->comparator_out;
						}
						else if(Search_control_nodes(NULL,control_ret,endnode,comp->condition_value,NULL)){
							if(!control_ret->result_control) control_ret->result_control=loop_block;
							else Insert_in_control_list(control_ret->result_control,loop_block);
							control_ret->control_out = endnode;
							tmpvar->comparator_out->condition_value = endnode;
							endnode->comparator_out = tmpvar->comparator_out;
							if(!loop_block->control_in) loop_block->control_in = control_ret;
							else Insert_in_control_list(loop_block->control_in,control_ret);
						}
					}
					tmpvar->comparator_out->value_out = new DeclareData;
					assign_value(tmpvar->comparator_out->value_out,comp->value_out);
					//now in this case, the break condition cannot be checked since the dfgnode doesnt contain a comparator node
					tmpvar = tmpvar->comparator_out->value_out;
				}
			}
			else tmpvar=NULL;
			tmpnode = loop_list[++i];
	}while(tmpnode && tmpvar);





}





//EDITING HERE!

//function to iteratively check the parents of node whose output is tmpinput if they are created in basic_blocks already. if not created, then its created until the  sent externally to this function
//in the end, it is checke if tmpinput is already present in any basic_block. 
//

//control_search is a null node, in which a value is being passed iternally while recursively calling it. its the control block from where the insertion of tmpinput is started
bool Check_parent_nodes(DeclareData *tmpinput, State_var *first_state,Control_block *control_search,Control_block*& control_ret,DeclareData*& endnode,Basic_block*& block_ret){


//DeclareData *tmpinput=NULL;
Control_block *tmpcontrol=NULL;
State_var *tmpstate=NULL;
State_var *state_list[10];
int i=0;
State_var *ret_state=NULL;
bool flag=false;
bool search=false;
Path_list *node=NULL;
Operate_op *tmpop=NULL;
Equal_to_op *tmpeq=NULL;
Equal_to_op *eqnode=NULL;
Place_block *tmpplace=NULL;
Transition_block *tmptran=NULL;
DFG_block *tmpdfg=NULL;
DeclareData *tmp_arr[50];


node = new Path_list;
Initialize_array_pointer(node);

while(tmpinput){
	
			//call this function to get the node which generated tmpinput and then continue the while loop with the input of that node.search only in tmpstate
		if(Search_dominator_of_node(tmpinput,NULL,node,first_state,NULL,false,false,true,true,block_ret,tmp_arr,NULL)){
				if(node->placenode){
					 tmpplace = node->placenode;
				//	else
					tmpinput = node->placenode->first_trans_node->data_node->assignment_graph->rhs_value;
				}
				else if(node->trannode){
					 tmptran = node->trannode;
				//	else
					tmpinput = node->trannode->data_node->assignment_graph->rhs_value;
				}
				else if(node->eqnode){
					 tmpeq = node->eqnode;
					//else
					tmpinput = node->eqnode->rhs_value;
				}
				else if(node->opnode){
					
						tmpinput = node->opnode->op1;
						tmpop = node->opnode;
						while(tmpinput){
						//	if(flag && Search_end_node_BasicBlock(tmpinput,tmpcontrol->bb_ptr,endnode,control_ret,false,block_ret,false,NULL) || Search_end_node_BasicBlock(tmpinput,first_basic_block,endnode,control_ret,true,block_ret,false,NULL)){
						//		Create_subnodes_under_endnode(endnode,NULL,control_ret,tmpcontrol->bb_ptr,NULL,block_ret,NULL,NULL,tmpop,node->opnode,'a');
							
						//	}
							if(Check_parent_nodes(tmpinput,first_state,control_search,control_ret,endnode,block_ret)){
								flag=true;
								break;
							}
							else{
								if(tmpinput == node->opnode->op1)
								tmpinput = node->opnode->op2;
								else tmpinput = NULL;
							}
						}
					if(flag) break;
					
				}
				else if(node->dfgnode){
					if(flag) tmpdfg = node->dfgnode;
					else{
						if(node->dfgnode->condition_op)
							tmpinput=node->dfgnode->condition_op->assign_expr->rhs_value;
						else if(node->dfgnode->assignment_graph)
							tmpinput = node->dfgnode->assignment_graph->rhs_value;
					}
				}
				
				
			}
			else{
				flag = true;
				break;
			}
		//}
}//endof while

		if(flag){
			//tmpinput is the varnode in petrigraph from where the insertion shud start
			//first get the controlblock and the basic block
			if(Trace_back_node(tmpinput,ret_state,first_state,NULL,state_list,true,true,NULL,true)){
				
				//tmpstate=ret_state;
				while(state_list[i]){
					
					if(Search_state_from_controlnode_list(state_list[i],first_control_node,control_search)){
						//Insert_path_in_BasicBlock(control_search,control_search->bb_ptr,tmpinput,first_state,NULL,false);
						//Create_subnodes_under_endnode(
						//check if tmpinput which was sent to this function, has been attached or not
						if(Search_end_node_BasicBlock(tmpinput,first_basic_block,endnode,control_ret,true,block_ret,false,NULL)){
							
							search = true;
							break;
						}
					}
					i++;
					//tmpstate= tmpstate->next_state;
				}
			}
		}		
		/*
		while(tmpinput){
			
			//if flag is true,tmpinput wont change
			if(flag && (Search_end_node_BasicBlock(tmpinput,tmpcontrol->bb_ptr,endnode,control_ret,false,block_ret,false,NULL) || Search_end_node_BasicBlock(tmpinput,first_basic_block,endnode,control_ret,true,block_ret,false,NULL)){
				if(tmpeq)
					Create_subnodes_under_endnode(endnode,NULL,control_ret,tmpcontrol->bb_ptr,NULL,block_ret,equalnode,tmpeq,NULL,NULL,'b');
				else if(tmpplace)
					Create_subnodes_under_endnode(endnode,NULL,control_ret,tmpcontrol->bb_ptr,tmpplace,block_ret,NULL,NULL,NULL,NULL,'p');
				else if(tmptran)
					Create_subnodes_under_endnode(endnode,NULL,control_ret,tmpcontrol->bb_ptr,NULL,block_ret,tmpeq,tmptran->data_node->assignment_graph,NULL,NULL,'t');
				else if(tmpdfg){
					if(tmpdfg->condition_op)
						eqnode = tmpdfg->condition_op->assign_expr;
					else if(tmpdfg->assignment_graph)
						eqnode = tmpdfg->assignment_graph;
					Create_subnodes_under_endnode(endnode,NULL,control_ret,tmpcontrol->bb_ptr,NULL,block_ret,tmpeq,eqnode,NULL,NULL,'b');
				}
			}
			else flag=false;
		}
		*/
		
	
//}


return search;

}




//function to check if header is the exit point of the loop. If header is traced depthwise and is connected to a comparator or signal selector or DFG,send true else check other nodes in the loop_list for the exit point, if any node leads to comp/SS/DFG, then return true

//exitpoint is the node from where the comparator node is connected directly or indirectly
//noderet is the node which contains the comparator/DFG/SS, only if checknode is true
//if checknode is false, then its already detected its a dataflow loop and must return the exitpoints of a dataflow loop in noderet.
//exitpoints of a dataflow loop means the nodes which lead away from the loop ,which do not involve the loop_header in their path
//searchflag is to indicate if the fn is called internally or externally. if true,called externally else false
//loop_header is the external node which leads to the entry node in the loop. Inside the fn, header is obtained as the entry node
bool Check_exitpoint_of_loop(Path_list *loop_header,Path_list *node_tmp,Path_list *nextnode,Path_list*& exitpoint,Path_list*& noderet,bool checknode,bool searchflag){

bool flag=false;
bool headerflag = false;
int i=0,num=0;
Place_block *tmp=NULL;
Equal_to_op *tmpeq=NULL;
Path_list *header = NULL;


//	noderet = new Path_list;
	//Initialize_array_pointer(noderet);

//trace just the header first to check if its connected to comparator/SS/DFG

//if(!loop_header) return flag;

if(!node_tmp){
	if(loop_header)
		//to search for the entry node in the loop which the loop_header node leads to
		Search_header_in_looplist(loop_header,header,nextnode,false,num);
	
	else header = loop_header;
	
}
else header = node_tmp;

if(header){
	if(header->varnode){
		if(checknode && Search_ControlNodes_depthwise(header->varnode,noderet,checknode,false,nextnode,true,exitpoint,true)){
			
			flag = true;
		}
		//for checking if header is one of the exit points of the dataflow loop//since checknode is false
		else if(!checknode && Search_header_in_nodepath(loop_header,header->varnode,noderet)){
			flag=true;
			exitpoint = noderet;
		}
		
	}
	else if(header->placenode){
		tmp = header->placenode;
		//while(tmp){
			if(checknode && Search_ControlNodes_depthwise(tmp->first_trans_node->output_var,noderet,checknode,false,nextnode,true,exitpoint,true)){
				flag = true;
				//break;
			}
			else if(!checknode && Search_header_in_nodepath(loop_header,tmp->first_trans_node->output_var,noderet)){
				flag=true;
				exitpoint = noderet;
				//break;
			}
			//else tmp = tmp->next_place;
		//}
	}
	else if(header->trannode){
		if(checknode && Search_ControlNodes_depthwise(header->trannode->output_var,noderet,checknode,false,nextnode,true,exitpoint,true)){
			flag=true;
			//noderet = header;
		}
		else if(!checknode && Search_header_in_nodepath(loop_header,header->trannode->output_var,noderet)){
			flag=true;
			exitpoint = noderet;
		}
		
	}
	else if(header->opnode){
		if(checknode && Search_ControlNodes_depthwise(header->opnode->output_value,noderet,checknode,false,nextnode,true,exitpoint,true)){
			flag=true;
			//noderet = header;
		}
		else if(!checknode && Search_header_in_nodepath(loop_header,header->opnode->output_value,noderet)){
			flag=true;
			exitpoint = noderet;
		}
	}
	else if(header->eqnode){
		tmpeq = header->eqnode;
			//EDITING HERE!
			if(checknode && Search_ControlNodes_depthwise(tmpeq->lhs_value,noderet,checknode,false,nextnode,true,exitpoint,true)){
				flag=true;
				//break;
			}
			else if(!checknode && Search_header_in_nodepath(loop_header,tmpeq->lhs_value,noderet)){
				flag= true;
				exitpoint = noderet;
				//break;
			}
			//tmpeq = tmpeq->next_equal;
		//}
	}
	else if(checknode && header->compnode){
		flag = true;
		noderet = header;
	}
	else if(checknode && header->signalnode){
		flag = true;
		noderet = header;
	}
//	else if(checknode && header->dfgnode)
//		flag = true;
	
}	
	//here,the flag to be raised if thefn is called internally
	if(!flag && searchflag){
		//this loop is for checking other nodes of the loop if header is not proved as the exit point OR if there is no header in the loop
		//here exitpoint may be more than 1
		while(loop_list[i]){
			if(!loop_list[i+1])
				break;
				
			else nextnode = loop_list[i+1];
			if(loop_list[i]!=loop_header && Check_exitpoint_of_loop(loop_header,loop_list[i],nextnode,exitpoint,noderet,checknode,false)){
				
				flag = true;
			}
			i++;
		}
	}


return flag;
	
}


//fn to search the loop entry node(header_ret) from the sent nodestart(which is an external node) and return the next node after the loop entry node(nextnode_ret)
//this fn when search_node is true, 
void Search_header_in_looplist(Path_list *nodestart , Path_list*& header_ret, Path_list*& nextnode_ret, bool search_node,int& index){

DeclareData *tmp = NULL , *tmpv = NULL;
bool search = false;
int i=0;

//nodestart(search_node = true) contains the starting header node in the loop.
if(nodestart->eqnode)
	tmp = nodestart->eqnode->lhs_value;
else if(nodestart->opnode)
	tmp = nodestart->opnode->output_value;
else if(nodestart->placenode)
	tmp = nodestart->placenode->first_trans_node->output_var;
else if(nodestart->trannode)
	tmp = nodestart->trannode->output_var;
else if(nodestart->compnode)
	tmp = nodestart->compnode->value_out;
else if(nodestart->signalnode)
	tmp = nodestart->signalnode->out_signal;
	
while(loop_list[i]){
	if(loop_list[i]->varnode){
		if(!search_node && !strcmp(tmp->name , loop_list[i]->varnode->name)){
			header_ret = loop_list[i];
			index = i;
			nextnode_ret = loop_list[++i];
			break;
		}
		//check for the output of nodestart which is an input of loop_list node, send that i back
		/*
		else if(search_node && !strcmp(loop_list[i]->varnode->name,tmp->name)){
			index = i;
			search = true;
			break;
		}*/
	}
	else if(loop_list[i]->eqnode){
		if(!search_node && !strcmp(tmp->name , loop_list[i]->eqnode->rhs_value->name)){
			header_ret = loop_list[i];
			index = i;
			nextnode_ret = loop_list[++i];
			if(!nextnode_ret) nextnode_ret = loop_list[0];
			break;
		}
		else if(search_node && !strcmp(loop_list[i]->eqnode->rhs_value->name,tmp->name)){
			index = i;
			search = true;
			break;
		}
	}
	else if(loop_list[i]->opnode){
		tmpv = loop_list[i]->opnode->op1;
		do{
			if(!search_node && !strcmp(tmp->name , tmpv->name)){
				header_ret = loop_list[i];
				index = i;
				nextnode_ret = loop_list[++i];
				if(!nextnode_ret) nextnode_ret = loop_list[0];
				break;
			}
			else if(search_node && !strcmp(tmp->name,tmpv->name)){
				index = i;
				search = true;
				break;
			}
			
			if(!search_node && tmpv == loop_list[i]->opnode->op1)
				tmpv = loop_list[i]->opnode->op2;
			else tmpv = NULL;
			
		}while( tmpv);
		
	}
	else if(loop_list[i]->placenode){
		tmpv = loop_list[i]->placenode->first_place_input;
		while( tmpv){
			if(!search_node && !strcmp(tmp->name,tmpv->name)){
				header_ret = loop_list[i];
				index = i;
				nextnode_ret = loop_list[++i];
				if(!nextnode_ret) nextnode_ret = loop_list[0];
				break;
			}
			else if(search_node && !strcmp(tmp->name,tmpv->name)){
				index = i;
				search = true;
				break;
			}
			tmpv = tmpv->next_n;
		}
		
	}
	else if(loop_list[i]->trannode){
		if(!search_node && !strcmp(tmp->name , loop_list[i]->trannode->data_node->assignment_graph->rhs_value->name)){
			header_ret = loop_list[i];
			index = i;
			nextnode_ret = loop_list[++i];
			if(!nextnode_ret) nextnode_ret = loop_list[0];
			break;
		}
		else if(search_node && !strcmp(tmp->name,loop_list[i]->trannode->data_node->assignment_graph->rhs_value->name)){
			index = i;
			search = true;
			break;
		}
	}
	if(!search_node && header_ret) break;
	else if(search_node && search) break;
	i++;
	
}


}





//the function is true when the node-loop_header is NOT found in the nodepath,which means you have found theexit node. start searching from varsearch
//called only if the loop is a dataflow loop

bool Search_header_in_nodepath(Path_list *loop_header,DeclareData *varstart,Path_list*& exit_ret){

DeclareData *tmp = NULL;
Place_block *tmp_pl = NULL;
Path_list *tmpnode = NULL;
Equal_to_op *tmpeq = NULL;
bool search = true;

if(varstart->place_ptr){
	tmp_pl = varstart->place_ptr;
	while(tmp_pl){
		Insert_in_pathlist_list(tmpnode,tmp_pl,NULL,NULL,NULL,NULL,NULL,NULL);
		if(Search_path_list(tmpnode,tmp_pl,NULL,NULL,NULL,NULL,NULL,NULL)){
			search = false;	
			Initialize_array_pointer(tmpnode);
			delete tmpnode;tmpnode = NULL;
		}
		else {search = true;break;}
		tmp_pl = tmp_pl->next_place;
	}
	if(search) Insert_node_in_pathlist(exit_ret,tmpnode);
	
}
if(varstart->transition_out){
	Insert_in_pathlist_list(tmpnode,NULL,varstart->transition_out,NULL,NULL,NULL,NULL,NULL);
	if(Search_path_list(tmpnode,NULL,varstart->transition_out,NULL,NULL,NULL,NULL,NULL)){
		search = false;
		Initialize_array_pointer(tmpnode);
		delete tmpnode;tmpnode = NULL;
	}
	else{
		 search = true;
		Insert_node_in_pathlist(exit_ret,tmpnode);
	}
}
if(varstart->equal_op_out){
	tmpeq = varstart->equal_op_out;
	while(tmpeq){
		Insert_in_pathlist_list(tmpnode,NULL,NULL,tmpeq,NULL,NULL,NULL,NULL);
		if(Search_path_list(tmpnode,NULL,NULL,tmpeq,NULL,NULL,NULL,NULL)){
			search = false;
			Initialize_array_pointer(tmpnode);
			delete tmpnode;tmpnode = NULL;
		}
		else{
			 search = true;
			 Insert_node_in_pathlist(exit_ret,tmpnode);
		}
		tmpeq = tmpeq->next_equal;
	}
}
if(varstart->operator_out){
	Insert_in_pathlist_list(tmpnode,NULL,NULL,NULL,varstart->operator_out,NULL,NULL,NULL);
	if(Search_path_list(tmpnode,NULL,NULL,NULL,varstart->operator_out,NULL,NULL,NULL)){
		search = false;
		Initialize_array_pointer(tmpnode);
		delete tmpnode;tmpnode = NULL;
	}
	else {
		search = true;
		Insert_node_in_pathlist(exit_ret,tmpnode);
	}
}
/*
if(varstart->comparator_out){
	Insert_in_pathlist_list(exit_ret,NULL,NULL,NULL,NULL,varstart->comparator_out,NULL,NULL);
	if(Search_path_list(exit_ret,NULL,NULL,NULL,NULL,NULL,varstart->comparator_out,NULL)){
		search = false;
		Initialize_array_pointer(exit_ret);
		delete exit_ret;exit_ret = NULL;
	}
	else{
		 search = true;
	
	}
}
if(varstart->signal_selector_out){
	Insert_in_pathlist_list(exit_ret,NULL,NULL,NULL,NULL,NULL,NULL,varstart->signal_selector_out);
	if(Search_path_list(exit_ret,NULL,NULL,NULL,NULL,NULL,NULL,varstart->signal_selector_out)){
		search = false;
		Initialize_array_pointer(exit_ret);
		delete exit_ret;exit_ret = NULL;
	}
	else search = true;
}
*/

return search;

}


//searchnode is an output of a node in loop_list

//function to search depthwise starting from searchnode,and return true once a comparator/SS/DFG is found in the depthwise search path
//nodeflag is to indicate if the comparator or SS or DFG found,must be returned via node_ret or not
//if true,must send else not.
//dfg_check is to indicate if it is being called to search in DFGgraph or petrigraph, if true, the fn should not check the dfgnode_out from searchnode
//searchflag is to indicate if the nextnode is to be checked or not
//EDITING NOW!!
bool Search_ControlNodes_depthwise(DeclareData *searchnode,Path_list*& node_ret,bool nodeflag,bool dfg_check,Path_list *nextnode,bool start,Path_list*& node_connect,bool searchflag){

bool flag = false;
//bool start = true;
DeclareData *tmp=NULL;
DeclareData *var = NULL;
Equal_to_op *tmpeq=NULL;
Place_block *tmp_pl = NULL;

tmp = searchnode;
if(searchflag){
	if(nextnode->placenode)
		var = nextnode->placenode->first_trans_node->output_var;
	else if(nextnode->trannode)
		var = nextnode->trannode->output_var;
	else if(nextnode->opnode){
		var= nextnode->opnode->output_value;
	}
	else if(nextnode->eqnode)
		var = nextnode->eqnode->lhs_value;
	else if(nextnode->varnode)
		var = nextnode->varnode;
}

while(tmp){
	if(searchflag && !start && !strcmp(tmp->name,var->name)){
		flag = false;
		break;
	}
	start = false;
	if(tmp->comparator_out){
		if(nodeflag){
			Insert_in_pathlist_list(node_ret,NULL,NULL,NULL,NULL,tmp->comparator_out,NULL,NULL);
			//node_ret = new Path_list;
		//	Initialize_array_pointer(node_ret);
			//node_ret->compnode = tmp->comparator_out;
		}
		flag = true;
		break;
	}
	else if(tmp->signal_selector_out){
		if(nodeflag){
			Insert_in_pathlist_list(node_ret,NULL,NULL,NULL,NULL,NULL,NULL,tmp->signal_selector_out);
		//	node_ret = new Path_list;
		//	Initialize_array_pointer(node_ret);
		//	 node_ret->signalnode = tmp->signal_selector_out;
		}
		flag = true;
		break;
	}
	else if(!dfg_check && tmp->dfgnode_out){
		if(nodeflag){
			Insert_in_pathlist_list(node_ret,NULL,NULL,NULL,NULL,NULL,tmp->dfgnode_out,NULL);
	//		node_ret = new Path_list;
	//		Initialize_array_pointer(node_ret);
	//		 node_ret->dfgnode = tmp->dfgnode_out;
		}
		flag = true;
		break;
	}
	if(!flag && tmp->equal_op_out){
		tmpeq = tmp->equal_op_out;
		while(tmpeq){
			if(Search_ControlNodes_depthwise(tmpeq->lhs_value,node_ret,nodeflag,dfg_check,nextnode,start,node_connect,searchflag)){
				flag = true;
				Insert_in_pathlist_list(node_connect,NULL,NULL,tmpeq,NULL,NULL,NULL,NULL);
				break;
			}
			tmpeq = tmpeq->next_equal;
		}
		if(flag) break;
	}
	if(!flag && tmp->operator_out){
		if(tmp->operator_out->op_type == '<'){
			if(nodeflag){
				Insert_in_pathlist_list(node_ret,NULL,NULL,NULL,tmp->operator_out,NULL,NULL,NULL);
			//	node_ret = new Path_list;
			//	Initialize_array_pointer(node_ret);
			//	node_ret->opnode = tmp->operator_out;
			}
			flag = true;
			break;
		}
		else if(Search_ControlNodes_depthwise(tmp->operator_out->output_value,node_ret,nodeflag,dfg_check,nextnode,start,node_connect,searchflag)){
			flag=true;
			Insert_in_pathlist_list(node_connect,NULL,NULL,NULL,tmp->operator_out,NULL,NULL,NULL);
			break;
		}
	}
	if(!flag && tmp->transition_out){
		if(Search_ControlNodes_depthwise(tmp->transition_out->output_var,node_ret,nodeflag,dfg_check,nextnode,start,node_connect,searchflag)){
			flag=true;
			Insert_in_pathlist_list(node_connect,NULL,tmp->transition_out,NULL,NULL,NULL,NULL,NULL);
			break;
		}
	}
	//if place is encountered, then come out of the loop, as it will never lead to a comparator following a place.
	if(!flag && tmp->place_ptr){
		flag = false;
		break;
		
	}
	else tmp = NULL;

}


return flag;
}


//ALGORITHM 1
//while searching for dominator,do not check state
//search_BasicBlock is to indicate if thefn to search in a DFG graph or petrinet model 
bool Search_Header_of_loop(State_var *first_state,Path_list*& node,bool search_BasicBlock){

int i=0;
Path_list *dominator_tmp=NULL , *node_tmp = NULL;
DeclareData *tmpvar=NULL;
DeclareData *inputs=NULL;
Basic_block *block_ret = NULL;
bool search = false;
DeclareData *arr_tmp[50];

node = new Path_list;
Initialize_array_pointer(node);

node_tmp = new Path_list;
Initialize_array_pointer(node_tmp);

while(loop_list[i] && !search){
	search = false;
	if(loop_list[i]->varnode){
		i++;
		continue;
	}
	if(!search && loop_list[i]->placenode){
		//search for the node whose output is the rhs_value of the placenode->first_trans_node->data_node->assignment_graph
		//CHANGED HERE
		tmpvar = loop_list[i]->placenode->first_trans_node->output_var;
		dominator_tmp = node_tmp;
		
		if(Search_dominator_of_node(tmpvar,NULL,dominator_tmp,first_state,NULL,false,false,true,search_BasicBlock,block_ret,arr_tmp,NULL)){
		
			while(dominator_tmp){
				//EDITING HERE!!
				//only if the place is not the parent node which is in the loop
				if(dominator_tmp->placenode){
					inputs = dominator_tmp->placenode->first_trans_node->data_node->condition_op->assign_expr->rhs_value;
					if(Search_dominator_of_node(inputs,NULL,node,first_state,NULL,false,false,false,search_BasicBlock,block_ret,arr_tmp,NULL)){
						search = true;
						break;
					}
					//else Initialize_array_pointer(node);
				}
				dominator_tmp = dominator_tmp->next_node;
			}
			if(search) break;
			else{
				 Initialize_array_pointer(node);
				 Initialize_array_pointer(node_tmp);
			}
		
		}
		else{
			 search = false;
			 Initialize_array_pointer(dominator_tmp);
		}
	}
	if(!search && loop_list[i]->trannode){
		//in this case, only one output will lead directly to a transition, but more than one node with same output can lead to one trannode
		tmpvar = loop_list[i]->trannode->output_var;
		dominator_tmp = node_tmp;
		if(Search_dominator_of_node(tmpvar,NULL,dominator_tmp,first_state,NULL,false,false,true,search_BasicBlock,block_ret,arr_tmp,NULL)){
		
			while(dominator_tmp){
				if(dominator_tmp->trannode){
					inputs = dominator_tmp->trannode->data_node->assignment_graph->rhs_value;
					if(Search_dominator_of_node(inputs,NULL,node,first_state,NULL,false,false,false,search_BasicBlock,block_ret,arr_tmp,NULL)){
						search = true;
						break;	
					}
					//else  Initialize_array_pointer(node);
				}
				dominator_tmp = dominator_tmp->next_node;
			}
			if(search) break;
			else{
				 Initialize_array_pointer(node);
				 Initialize_array_pointer(node_tmp);
			}
		}
		else{
			 search = false;
			 Initialize_array_pointer(dominator_tmp);
		}
	}
		
	if(!search && loop_list[i]->opnode){
		//here we must search both the inputs of opnode ,and search which input is not part of the loop
		//EDITING HERE!
		tmpvar = loop_list[i]->opnode->output_value;
		dominator_tmp = node_tmp;
			if(Search_dominator_of_node(tmpvar,NULL,dominator_tmp,first_state,NULL,false,false,true,search_BasicBlock,block_ret,arr_tmp,NULL)){
		
				inputs = dominator_tmp->opnode->op1;
				do{
					if(inputs->data_type!= integer && Search_dominator_of_node(inputs,NULL,node,first_state,NULL,false,false,false,search_BasicBlock,block_ret,arr_tmp,NULL)){
						search = true;
						break;
					}
					//else Initialize_array_pointer(node);

					if(inputs == dominator_tmp->opnode->op1)
						inputs = dominator_tmp->opnode->op2;
					else inputs = NULL;
				}while(inputs);
				
				if(!search){
					 Initialize_array_pointer(node);
					 Initialize_array_pointer(node_tmp);
				}
			}
			else
				Initialize_array_pointer(dominator_tmp);
			if(search) break;	
			
	}
	
	if(!search && loop_list[i]->eqnode){
		tmpvar = loop_list[i]->eqnode->lhs_value;
		dominator_tmp = node_tmp;
		if(Search_dominator_of_node(tmpvar,NULL,dominator_tmp,first_state,NULL,false,false,true,search_BasicBlock,block_ret,arr_tmp,NULL)){
			while(dominator_tmp){
				//one dominator is assumed to be loop_list->eqnode,and only if there is another dominator whch is placenode, that node is checked
				if(dominator_tmp->placenode){
					inputs = dominator_tmp->placenode->first_trans_node->data_node->condition_op->assign_expr->rhs_value;
					if(Search_dominator_of_node(tmpvar,NULL,node,first_state,NULL,false,false,false,search_BasicBlock,block_ret,arr_tmp,NULL)){
						search = true;
						break;
					}
					else Initialize_array_pointer(node);
				}
				dominator_tmp = dominator_tmp->next_node;
			}
			if(search) break; 
			else{
				 Initialize_array_pointer(node);
				 Initialize_array_pointer(node_tmp);
			}
		}
		else Initialize_array_pointer(dominator_tmp);
		//if(search) break;
		
	}
	
	// no need of checking comparators and signal selectors, since they do not form part of the loop

	i++;
}

if(!search){
	delete node;node = NULL;
}
delete_node_list(node_tmp);

return search;

}

//DFG search
//fn to search an output or input variable node in the search_block
bool Search_node_in_PortList(DeclareData *nodetosearch,Basic_block *search_block,bool outputflag){

DeclareData *tmp = NULL;
bool search = false;

if(outputflag)
	 tmp = search_block->first_block_output;
	 
else 	tmp = search_block->first_block_input;
 
 while(tmp){
 	if(!strcmp(nodetosearch->name,tmp->name)){
 		search = true;
 		break;
 	}
 	tmp = tmp->next_n;
 }


return search;

}


//both petri and DFGgraph
//only searches in DFG_basicblock and not control node
//this function is to search the searchvar which must be generated by a previous node, the dominator of tmp. 
//part_of_loop is to indicate if you want to search the path_list if its a part of path_list OR if its not a part of path_list
//fn starts search from the first_place_node and not from the first_state
//flag is to indicate if the function is called externally or internally, if flag=false, then its called from outside else called internally
//this fn also searches the list of dominators of searchvar i.e list of nodes which have generated searchvar.
//dominator_only indicates that the fn is called only to find the dominators of searchvar and not search in path_list
//search_basic_block flag to indicate if its supposed to search the DFG,hence must search other basic_blocks, if true, send the block where the node was found
bool Search_dominator_of_node(DeclareData *searchvar ,DeclareData *varstart, Path_list*& node,State_var *first_state,State_var *state,bool flag,bool part_of_loop,bool dominator_only,bool search_basic_block,Basic_block*& block_ret,DeclareData** dom_arrptr,Basic_block *tmp_block){

State_var *tmp_state = NULL;
//Transition_block *tmp_tran = NULL;
bool search = false;
bool loop_start = true;
DeclareData *tmpvar=NULL;
Place_block *tmp_pl=NULL;
DeclareData *first_input = NULL;
Transition_block *tmps=NULL;
Compare_operator *tmpc=NULL;
Equal_to_op *tmpeq=NULL;
//Basic_block *tmp_block = NULL;
Signal_selector *tmpsig=NULL;



if(!flag && !search_basic_block){
	tmp_state = first_state;
	//tmp_tran = first_place_node->first_trans_node;
	Initialize_array(dom_arrptr,50);
}

else if(flag && !search_basic_block){
	tmp_state = state;
	 if(Check_node_from_array(dom_arrptr,50,varstart))
	 	loop_start = false;	
}

else if(search_basic_block){
	if(!flag){
		first_input = first_basic_block->first_block_input;
		tmp_block = first_basic_block;
		Initialize_array(dom_arrptr,50);
	}
	else{
		if(Check_node_from_array(dom_arrptr,50,varstart))
			loop_start = false;
		else
			first_input = varstart;	
		
	}
}	
	
while(loop_start && (tmp_state || first_input)){
	if(!flag && !search_basic_block) tmpvar = tmp_state->state_name;
	else if(flag && !search_basic_block) tmpvar = varstart;
	else if(search_basic_block){
		//if(first_input)
			 tmpvar = first_input;
	//	else
		//	tmpvar = tmp_block->first_block_input;
	}
	while(tmpvar){
	
		Change_node_in_array(dom_arrptr,50,tmpvar,true); //insert here
			//TO BE CHANGED HERE--- next_trans_node option to be added here
		if(tmpvar->place_ptr){
			tmp_pl = tmpvar->place_ptr;
			while(tmp_pl && Search_var_in_InputList(tmpvar,tmp_pl,NULL)){
				if(!strcmp(searchvar->name , tmp_pl->first_trans_node->output_var->name)){
					//node->placenode = tmp_pl;
					if(dominator_only){
						if(!node->placenode) node->placenode = tmp_pl;
						else Insert_in_pathlist_list(node,tmp_pl,NULL,NULL,NULL,NULL,NULL,NULL);
						search = true;
					}
					else if(!dominator_only && part_of_loop){
						//Initialize_array_pointer(node);
						
						if( Search_path_list(node,tmp_pl,NULL,NULL,NULL,NULL,NULL,NULL)){
							search = true;
							node->placenode = tmp_pl;
							break;
						}
						//else
							//node->placenode=NULL;
					}
					else if(!dominator_only && !part_of_loop){
						//Initialize_array_pointer(node);
						
						if( !Search_path_list(node,tmp_pl,NULL,NULL,NULL,NULL,NULL,NULL)){
							node->placenode = tmp_pl;
							search = true;
							break;
						}
						//else
							//node->placenode=NULL; 
					}
					else
						node->placenode=NULL;
				}
				else if(Search_dominator_of_node(searchvar,tmp_pl->first_trans_node->output_var,node,first_state,tmp_state,true,part_of_loop,dominator_only,search_basic_block,block_ret,dom_arrptr,tmp_block)){
					search = true;
					//break;
				}	
				
				tmp_pl = tmp_pl->next_place;
				//tmpvar = tmpvar->place_ptr->first_trans_node->output_var;
			}
			//if(search) break;
			
		}
		if(tmpvar->transition_out){
			tmps = tmpvar->transition_out;
			while(tmps){
				//tmpvar = tmps->output_var;			
				if(!strcmp(searchvar->name,tmps->output_var->name)){
					//node->trannode = tmps;
					if(dominator_only){
						if(!node->trannode) node->trannode = tmps;
						else Insert_in_pathlist_list(node,NULL,tmps,NULL,NULL,NULL,NULL,NULL);
						search = true;
					}
					else if(!dominator_only && part_of_loop){
						//Initialize_array_pointer(node);
						
						if( Search_path_list(node,NULL,tmps,NULL,NULL,NULL,NULL,NULL)){
							search=true;
							node->trannode = tmps;
							break;
						}
						//else node->trannode=NULL;
					}
					else if(!dominator_only && !part_of_loop){
						//Initialize_array_pointer(node);
						
						if( !Search_path_list(node,NULL,tmps,NULL,NULL,NULL,NULL,NULL)){
							search = true;
							node->trannode = tmps;
							break;
						}
						//else node->trannode=NULL;
					}
					else node->trannode=NULL;
				}
				else if(Search_dominator_of_node(searchvar,tmps->output_var,node,first_state,tmp_state,true,part_of_loop,dominator_only,search_basic_block,block_ret,dom_arrptr,tmp_block)){
					search = true;
					//break;
				}
				tmps = tmps->next_trans_node;
				if(tmps && tmps->traverse_node)
					continue;
				else tmps = NULL;
			}
			//if(search) break;
			
		}
		if(tmpvar->comparator_out && !search_basic_block){
			tmpc = tmpvar->comparator_out;
			while(tmpc){
				//tmpvar = tmpc->value_out;
				if(!strcmp(searchvar->name,tmpc->value_out->name)){
					//node->compnode = tmpc;
					if(dominator_only){
						if(!node->compnode) node->compnode = tmpc;
						else Insert_in_pathlist_list(node,NULL,NULL,NULL,NULL,tmpc,NULL,NULL);
						search = true;
					}
					else if(!dominator_only && part_of_loop){
						//Initialize_array_pointer(node);
						
						if( Search_path_list(node,NULL,NULL,NULL,NULL,NULL,tmpc,NULL)){
							search=true;
							node->compnode = tmpc;
							break;
						}
						//else node->compnode=NULL;
					}
					else if(!dominator_only && !part_of_loop){
						//Initialize_array_pointer(node);
						
						if( !Search_path_list(node,NULL,NULL,NULL,NULL,NULL,tmpc,NULL)){
							search = true;
							node->compnode = tmpc;
							break;
						}
						//else node->compnode=NULL;
					}
					else node->compnode=NULL;
				}
				else if(Search_dominator_of_node(searchvar,tmpc->value_out,node,first_state,tmp_state,true,part_of_loop,dominator_only,search_basic_block,block_ret,dom_arrptr,tmp_block)){
					search = true;
					//break;
				}
				tmpc = tmpc->next_comparator;
			}
			//if(search) break;
		}
		if( tmpvar->equal_op_out){
			tmpeq = tmpvar->equal_op_out;
			while(tmpeq){
				//tmpvar = tmpeq->lhs_value;
				if(!strcmp(searchvar->name,tmpeq->lhs_value->name)){
					//node->eqnode= tmpeq;
					if(dominator_only){
						if(!node->eqnode) node->eqnode = tmpeq;
						else Insert_in_pathlist_list(node,NULL,NULL,tmpeq,NULL,NULL,NULL,NULL);
						search = true;
					}
					else if(!dominator_only && part_of_loop){
						//Initialize_array_pointer(node);
						
						if( Search_path_list(node,NULL,NULL,tmpeq,NULL,NULL,NULL,NULL)){
							search=true;
							node->eqnode= tmpeq;
							break;
						}
						//else node->eqnode=NULL;
					}
					else if(!dominator_only && !part_of_loop){
						//Initialize_array_pointer(node);
						if( !Search_path_list(node,NULL,NULL,tmpeq,NULL,NULL,NULL,NULL)){
							search = true;
							node->eqnode= tmpeq;
							break;
						}
						//else node->eqnode=NULL;
					}
					else node->eqnode=NULL;
				}
				else if(Search_dominator_of_node(searchvar,tmpeq->lhs_value,node,first_state,tmp_state,true,part_of_loop,dominator_only,search_basic_block,block_ret,dom_arrptr,tmp_block)){
					search = true;
					//break;
				}
				tmpeq = tmpeq->next_equal;
			}
		//	if(search) break;
		}
		if(tmpvar->operator_out){
			//tmpvar = tmpvar->operator_out->output_value;
			if(!strcmp(searchvar->name,tmpvar->operator_out->output_value->name)){
				//node->opnode = tmpvar->operator_out;
				if(dominator_only){
					if(!node->opnode) node->opnode = tmpvar->operator_out;
					else Insert_in_pathlist_list(node,NULL,NULL,NULL,tmpvar->operator_out,NULL,NULL,NULL);
					search = true;
				}
				else if(!dominator_only && part_of_loop){
					//Initialize_array_pointer(node);
					if(Search_path_list(node,NULL,NULL,NULL,tmpvar->operator_out,NULL,NULL,NULL)){
						search=true;
						node->opnode = tmpvar->operator_out;
						break;
					}
					//else node->opnode = NULL;
				}
				else if(!dominator_only && !part_of_loop){
					//Initialize_array_pointer(node);
					if(!Search_path_list(node,NULL,NULL,NULL,tmpvar->operator_out,NULL,NULL,NULL)){
						search = true;
						node->opnode = tmpvar->operator_out;
						break;
					}
					//else node->opnode = NULL;
				}
				
			}
			else if(Search_dominator_of_node(searchvar,tmpvar->operator_out->output_value,node,first_state,tmp_state,true,part_of_loop,dominator_only,search_basic_block,block_ret,dom_arrptr,tmp_block)){
				search = true;
				//break;
			}
			
		}
		if(tmpvar->dfgnode_out && !search_basic_block){
			// here the output of the dfg node is the same as the output of the switchcase node
			if(!strcmp(searchvar->name,tmpvar->dfgnode_out->output->name)){
				//node->dfgnode = tmpvar->dfgnode_out;
				if(dominator_only){
					if(!node->dfgnode) node->dfgnode = tmpvar->dfgnode_out;
					else Insert_in_pathlist_list(node,NULL,NULL,NULL,NULL,NULL,tmpvar->dfgnode_out,NULL);
					search = true;
				}
				else if(!dominator_only && part_of_loop){
					//Initialize_array_pointer(node);
					if(Search_path_list(node,NULL,NULL,NULL,NULL,tmpvar->dfgnode_out,NULL,NULL)){
						search=true;
						node->dfgnode = tmpvar->dfgnode_out;
						break;
					}
					//else node->dfgnode=NULL;
				}
				else if(!dominator_only && !part_of_loop){
					//Initialize_array_pointer(node);
					if( !Search_path_list(node,NULL,NULL,NULL,NULL,tmpvar->dfgnode_out,NULL,NULL)){
						search = true;
						node->dfgnode = tmpvar->dfgnode_out;
						break;
					}
					//else node->dfgnode = NULL;
				}
			}
			else
				node->dfgnode=NULL;
			if(!search){
				tmpvar = tmpvar->dfgnode_out->output;
				continue;
			}
			
		}
		if(tmpvar->signal_selector_out && !search_basic_block){
			tmpsig = tmpvar->signal_selector_out;
			while(tmpsig){
				tmpvar = tmpsig->out_signal;
				if(!strcmp(searchvar->name , tmpvar->name)){
					node->signalnode = tmpsig;
					if(dominator_only){
						if(!node->signalnode) node->signalnode = tmpsig;
						else Insert_in_pathlist_list(node,NULL,NULL,NULL,NULL,NULL,NULL,tmpsig);
						search = true;
					}
					else if(!dominator_only && part_of_loop){
						//Initialize_array_pointer(node);
						if(Search_path_list(node,NULL,NULL,NULL,NULL,NULL,NULL,tmpsig)){
							node->signalnode = tmpsig;
							search = true;
							break;
						}
						//else node->signalnode = NULL;
					}
					else if(!dominator_only && !part_of_loop){
						//Initialize_array_pointer(node);
						if( !Search_path_list(node,NULL,NULL,NULL,NULL,NULL,NULL,tmpsig)){
							search = true;
							node->signalnode = tmpsig;
							break;
						}
						//else node->signalnode = NULL;
					}
					else	node->signalnode=NULL;
					
				}
				else if(Search_dominator_of_node(searchvar,tmpvar,node,first_state,tmp_state,true,part_of_loop,dominator_only,search_basic_block,block_ret,dom_arrptr,tmp_block)){
					search = true;
					//break;
				}
				tmpsig = tmpsig->next_selector;
			}
			//if(search) break;
		}
		//if(!search)
		tmpvar=NULL;
	}
	//search flag must be stored here and sent back to the function..TO BE DONE
	if(!flag && !search_basic_block)
		tmp_state = tmp_state->next_state;
	else if(search_basic_block){
		first_input = first_input->next_n;
		if(!first_input || (tmpvar && Search_node_in_PortList(tmpvar,tmp_block,true)))
			tmp_block = tmp_block->next_block;
		//else tmp_block = NULL;
		
	}
		
	else tmp_state = NULL;
}


if(search)
	block_ret = tmp_block;


return search;

}


//fn to search a node in the place_input list or state_input list of place
bool Search_var_in_InputList(DeclareData *search_node , Place_block *place,Transition_block *tran){

DeclareData *tmp = NULL;
bool flag = false;

if(place){
	tmp = place->first_place_input;
	while(tmp){
		if(!strcmp(search_node->name,tmp->name)){
			flag = true;
			break;
		}
		tmp = tmp->next_n;
	}	
	if(!flag){
		tmp = place->state_place_input;
		while(tmp){
			if(!strcmp(search_node->name,tmp->name)){
				flag = true;
				break;
			}
			tmp = tmp->next_n;
		}
	}	
}
//only for case block 
else{
	if(tran->data_node->condition_op){
		if(tran->data_node->condition_op->equal_cond){
			tmp = tran->data_node->condition_op->equal_cond->lhs_value;
			if(!strcmp(tmp->name , search_node->name))
				flag = true;
		}
		else{
			if(!strcmp(search_node->name,tran->data_node->condition_op->assign_expr->rhs_value->name))
				flag = true;
			else if(tran->data_node->condition_op->if_cond_var && !strcmp(search_node->name , tran->data_node->condition_op->if_cond_var->name))
				flag = true;
		}
	}
	else if(tran->data_node->assignment_graph){
		flag = true;
	}
	
}


return flag;

}




//function to search the loop list if node is part of the loop or not
//this function is called two times. once its called,if node is part of loop.if node is part of loop search is true else search is false;

bool Search_path_list(Path_list *node,Place_block *place, Transition_block *tran, Equal_to_op *equal, Operate_op *operate, DFG_block *dfg, Compare_operator *comp, Signal_selector *sig){

//case:1 to search if node is part of the loop
//case 2: to search if node is not part of the loop



int i = 1;
bool search = false;
while(loop_list[i]){
	if(loop_list[i]->placenode && place && (place == loop_list[i]->placenode)){
		
		search = true;
		break;
	}
	if(loop_list[i]->trannode && tran && (tran == loop_list[i]->trannode)){
		
		search = true;
		
		break;
	}
	if(loop_list[i]->opnode && operate && (operate == loop_list[i]->opnode)){
		
		search = true;
		
		break;
	}
	if(loop_list[i]->eqnode && equal && (equal == loop_list[i]->eqnode)){
		
		search = true;
		
		break;
	}
	if(loop_list[i]->compnode && comp && (comp == loop_list[i]->compnode)){
		
		search = true;
		
		break;
	}
	if(loop_list[i]->signalnode && sig && (sig == loop_list[i]->signalnode)){
		
		search = true;
		
		break;
	}
	if(loop_list[i]->dfgnode && dfg && (dfg == loop_list[i]->dfgnode)){
		
		search = true;
		
		break;
	}
	i++;
	
}


return search;
}


//functionn to search searchvar in the array_ptr. send true if found else send false
bool Check_node_from_array(DeclareData** array_ptr,int size,DeclareData *searchvar){

DeclareData *tmp = NULL;
bool search = false;
int i=0;

for(i=0; i<size;i++){
	if(array_ptr[i] && !strcmp(searchvar->name,array_ptr[i]->name)){
		search = true;
		break;
	}
	else
		search = false;
	
}

return search;
}


//fn to insert or delete node in the array of pointers
void Change_node_in_array(DeclareData** arr_list, int size,DeclareData *node_d,bool changeflag){

DeclareData *tmp = NULL;
int i;


if(changeflag){
	for(i=0;i<size;i++){
		if(arr_list[i])
			continue;
		else
			break;
	}

	arr_list[i] = node_d;
	//arr_list[++i] = NULL;

}
else{
	arr_list[i] = NULL;
	
}



}

//this function searches in botbn DFG and petrigraph

//function to search the petri model or DFG for loop back sub-graphs,which is stored in a list node_list
//flag indicates if flag is true,then its a first call to th function externally else if flag=false, then its called internally
//check_path is to indicate if to create path_list.
//while searching for the loop,state must be checked, every state input to a node should be the same as the control_block in use currently
//Ediit thisfn for search for loop in Dataflowgraph also in basic block

//should also return back the first node after varend,which leads to a loop


//here, we can create an array of pointers holding the address of tmpvar each time tmpvar has some value. The array is passed to this function. When tmp is checked with varend, it should also be checked if its already in the array. If yes, then node is false, and go back to the last recursion and pop out the last element of the array until there is a next dominator. if there is anotehr dominator, no popping out is required
//searchnode is a flag to search a particular "searchvar" as output of a node inside the loop. if searchvar is true, searchvar is sent to be searched, and if found, the value is sent through searchvar.
bool Search_back_petri_model(DeclareData *varend ,DeclareData *tmpvar, bool flag,bool check_path,State_var *first_state,int& i,bool start,Path_list*& loopstart,bool startloop,DeclareData** arr_ptr,int arr_size,bool search_basicblock,Basic_block*& block_search_ret,bool searchnode,DeclareData*& searchvar){

DeclareData *tmp = NULL;
State_var *ret_state=NULL;
Place_block *place_st=NULL;
Transition_block *tran_st=NULL;
Equal_to_op *equal_st=NULL;
Compare_operator *comp_st=NULL;
DFG_block *dfg_st=NULL;
Operate_op *op_st=NULL;
Signal_selector *signal_st=NULL;
Path_list *dominator_ret = NULL;
Basic_block *block_ret = NULL;
bool node=false;
bool node_found = false;
bool search_dominator = true;
DeclareData *dom_arr[50];

if(flag) tmp=varend;
else tmp = tmpvar;

node = false;

if(flag)
	Initialize_array(arr_ptr,10);

//here compare tmp with the existing array list
//this fn sends true if tmp is found in arr_ptr
//tmp is already sent in that arr_ptr
else if(Check_node_from_array(arr_ptr,arr_size,tmp)){
	node = false;
	search_dominator = false;
	
}
// in the beginning both varend and tmp will be same, so should not compare
//only compare if its not found in array of pointers arr_ptr
else if(start && search_dominator && !strcmp(varend->name , tmp->name)){
	//if(!check_path) loop_list[i++]->varnode = tmp;
	node=true;

}
	start = true;
	if(!node && search_dominator){
		dominator_ret = new Path_list;
		Initialize_array_pointer(dominator_ret);
		if(!flag) Change_node_in_array(arr_ptr,arr_size,tmp,true); //since tmp is not in the array, insert tmp in the array here
		
		//here we only obtain the set of dominators of each tmp.this fn is creating the set of dominators
		node_found = Search_dominator_of_node(tmp,NULL,dominator_ret,first_state,NULL,false,false,true,search_basicblock,block_ret,dom_arr,NULL);
		if(node_found){
			while(dominator_ret){
				if(dominator_ret->placenode){
					if(dominator_ret->placenode->first_trans_node->data_node->assignment_graph)
						tmp = dominator_ret->placenode->first_trans_node->data_node->assignment_graph->rhs_value;
					else tmp = dominator_ret->placenode->first_trans_node->data_node->condition_op->assign_expr->rhs_value;
					
					if(Search_back_petri_model(varend,tmp , false,check_path,first_state,i,start,loopstart,startloop,arr_ptr,arr_size,search_basicblock,block_search_ret,searchnode,searchvar)){
						node=true;
						if(startloop) loopstart = dominator_ret;
						if(!check_path) loop_list[i++]->placenode = dominator_ret->placenode;
						if(search_basicblock) block_search_ret = block_ret;
						if(searchnode){
							//this case is for searching a variable in the loop -- here its confirmed that it is a loop
							if(!strcmp(searchvar->name,dominator_ret->placenode->first_trans_node->output_var->name)){
								node = true;
								searchvar = dominator_ret->placenode->first_trans_node->output_var;
								//break;
							}
						}
						
						if(node) delete_node_list(dominator_ret);
						//break;
					}
				
				}
				if(!node && dominator_ret->trannode){
					tmp = dominator_ret->trannode->data_node->assignment_graph->rhs_value;
					
					if(Search_back_petri_model(varend,tmp , false,check_path,first_state,i,start,loopstart,startloop,arr_ptr,arr_size,search_basicblock,block_search_ret,searchnode,searchvar)){
						node=true;
						if(startloop) loopstart = dominator_ret;
						if(!check_path) loop_list[i++]->trannode = dominator_ret->trannode;
						if(search_basicblock) block_search_ret = block_ret;
						if(searchnode){
							if(!strcmp(searchvar->name,dominator_ret->trannode->output_var->name)){
								node = true;
								searchvar = dominator_ret->trannode->output_var;
								//break;
							}
						}
						if(node) delete_node_list(dominator_ret);
					}
				
					else node=false;
				}
				if(!node && dominator_ret->eqnode){
					tmp = dominator_ret->eqnode->rhs_value;
					
					if(Search_back_petri_model(varend,tmp , false,check_path,first_state,i,start,loopstart,startloop,arr_ptr,arr_size,search_basicblock,block_search_ret,searchnode,searchvar)){
						node=true;
						if(startloop) loopstart = dominator_ret;
						if(!check_path) loop_list[i++]->eqnode = dominator_ret->eqnode;
						if(search_basicblock) block_search_ret = block_ret;
						if(searchnode){
							if(!strcmp(searchvar->name,dominator_ret->eqnode->lhs_value->name)){
								node = true;
								searchvar = dominator_ret->eqnode->lhs_value;
								//break;
							}
						}
						if(node) delete_node_list(dominator_ret);
					}
					else node=false;
				}
				if(!node && dominator_ret->opnode){
					
					op_st = dominator_ret->opnode;
					tmp = op_st->op1;
					do{
			
						if(Search_back_petri_model(varend,tmp , false,check_path,first_state,i,start,loopstart,startloop,arr_ptr,arr_size,search_basicblock,block_search_ret,searchnode,searchvar)){
							if(!check_path) loop_list[i++]->opnode= dominator_ret->opnode;
							if(startloop) loopstart = dominator_ret;
							node=true;
							if(search_basicblock) block_search_ret = block_ret;
							if(searchnode){
								if(!strcmp(searchvar->name,dominator_ret->opnode->output_value->name)){
									node = true;
									searchvar = dominator_ret->opnode->output_value;
								}
							}
							break;
						}
						
						if(op_st->op1->data_type!=integer && !strcmp(tmp->name , op_st->op1->name))
							tmp = op_st->op2;
						//else if(strcmp(tmp->name,op_st->op1->name)) tmp = op_st->op1;
						else tmp=NULL;
					}while(tmp);
					if(node) delete_node_list(dominator_ret);
				}
				//this part is only for petrigraph,dfgraph search should not use this
				if(!search_basicblock && !node && dominator_ret->compnode){
					if(!check_path) loop_list[i++]->compnode = dominator_ret->compnode;
					comp_st = dominator_ret->compnode;
					do{
					
						if(tmp && Search_back_petri_model(varend,tmp,false,check_path,first_state,i,start,loopstart,startloop,arr_ptr,arr_size,search_basicblock,block_search_ret,searchnode,searchvar)){
							if(startloop) loopstart = dominator_ret;
							node=true;
							if(search_basicblock) block_search_ret = block_ret;
							if(searchnode){
								if(!strcmp(searchvar->name,dominator_ret->compnode->value_out->name)){
									node = true;
									searchvar = dominator_ret->compnode->value_out;
								}
							}
							break;
						}
						
						if(comp_st->lhs_compare && !strcmp(tmp->name,comp_st->lhs_compare->name))
							tmp = comp_st->lhs_compare;
						else if(comp_st->condition_value) tmp = comp_st->condition_value;
						else tmp = NULL;
				
					}while(tmp);
					if(node) delete_node_list(dominator_ret);
				}
				//no signl selectors in a loop
				if(!node){
					dominator_ret = dominator_ret->next_node;
					if(!dominator_ret)
						Change_node_in_array(arr_ptr,arr_size,tmp,false);
				}
				
			}
		}
		else{
			node = false;
			delete dominator_ret ; dominator_ret= NULL;
		}
	}
	
	
return node;

}

//only for DFG graph
//function to search varsearch in a basic_block and return the node which generated this variable.
//search starts with the block_search->first_block_input and continues breadth wise with the ohter inputs of the block. if no block_search provided, it will check from the first_basic_block to search the node.
bool Search_back_BasicBlock_node(DeclareData *varsearch,DeclareData *tmpvar,Basic_block *block_search,Equal_to_op*& eq_ret,Operate_op*& op_ret){

DeclareData *tmp = NULL;
DeclareData *tmp_d = NULL;
Equal_to_op *tmpeq=NULL;
Basic_block *tmp_block = NULL;
Operate_op *tmpop = NULL;
bool flag = false;

if(block_search){
	tmp_block = block_search;
	tmp = block_search->first_block_input;	
}
else{
	tmp_block = first_basic_block;
	tmp = first_basic_block->first_block_input;
}


while(tmp_block){	
	tmp = tmp_block->first_block_input;
	while(tmp){
		flag = false;
		tmp_d = tmp;
		while(tmp_d){
			if(tmp_d->equal_op_out){
				tmpeq = tmp_d->equal_op_out;
				while(tmpeq){
					tmp_d = tmpeq->lhs_value;
					if(!strcmp(varsearch->name,tmp_d->name)){
						eq_ret = tmpeq;
						flag = true;
						break;
					}
					else if(Search_back_BasicBlock_node(varsearch,tmp_d,block_search,eq_ret,op_ret)){
						flag = true;
						break;
					}
					tmpeq = tmpeq->next_equal;
				}
				if(flag) break;
			}
			if(!flag && tmp_d->operator_out){
				tmpop = tmp_d->operator_out;
				while(tmpop){
					tmp_d = tmpop->output_value;
					if(!strcmp(varsearch->name,tmp_d->name)){
						op_ret = tmpop;
						flag = true;
						break;
					}
					else if(Search_back_BasicBlock_node(varsearch,tmp_d,block_search,eq_ret,op_ret)){
						flag= true;
						break;
					}
					tmpop = tmpop->next_oper;
				}
				if(flag) break;
			}
			else tmp_d = NULL;
			
		}//end of tmp_d while
		if(flag) break;
		
		tmp = tmp->next_n;
	}//end of tmp while
	
	if(!block_search)
		tmp_block = tmp_block->next_block;
	else tmp_block = NULL;

}//end of block while


return flag;
}






//only for petrigraph
//function to search a variable and return the node which has generated this variable, the search is done in top-bottom manner from the statenode
//there can be two nodes which can generate the same varsearch variable, thus this function must return both the nodes if its this case
bool Search_back_node(DeclareData *varsearch,DeclareData *tmpvar,State_var *first_state,State_var *state,Place_block*& place_ret,Transition_block*& tran_ret,Equal_to_op*& equal_ret,Operate_op*& op_ret,Compare_operator*& comp_ret, DFG_block*& dfg_ret,Signal_selector*& signal_ret){

DeclareData *tmp=NULL;
bool flag=false;
State_var *tmp_state=NULL;
Equal_to_op *tmp_eq=NULL;
Compare_operator *tmpcomp=NULL;
Signal_selector *tmpsig=NULL;
Place_block *placetmp=NULL;
//EDITING HERE FIRST
//change the fn in a way that if two nodes generate the same output, then, this function must return both the nodes.

if(!state)
	tmp_state = first_state;
else	tmp_state = state;


while(tmp_state){
	flag=false;
	if(!tmpvar)
		tmp = tmp_state->state_name;
	else	tmp = tmpvar;
	while(tmp){
		flag=false;
		if(tmp->place_ptr){
			placetmp = tmp->place_ptr;
			while(placetmp){
			
				tmp = placetmp->first_trans_node->output_var;
				if(!strcmp(tmp->name , varsearch->name)){
					place_ret = placetmp;
					flag=true;
					break;
				}
				else if(Search_back_node(varsearch,tmp,NULL,tmp_state,place_ret,tran_ret,equal_ret,op_ret,comp_ret,dfg_ret,signal_ret)){
					flag = true;
					break;
				}
				 placetmp = placetmp->next_place;
			}
			if(flag) break;
		}
		if(!flag && tmp->transition_out){
			tmp = tmp->transition_out->output_var;
			if(!strcmp(tmp->name, varsearch->name)){
				tran_ret = tmp->transition_out;
				flag=true;
				break;
			}
			else flag=false;
		}
		
		if(!flag && tmp->equal_op_out){
			tmp_eq = tmp->equal_op_out;
			while(tmp_eq){
				tmp = tmp_eq->lhs_value;
				if(!strcmp(tmp->name , varsearch->name)){
					equal_ret = tmp_eq;
					flag=true;
					break;
				}
				else if(Search_back_node(varsearch,tmp,NULL,tmp_state,place_ret,tran_ret,equal_ret,op_ret,comp_ret,dfg_ret,signal_ret)){
					flag=true;
					break;
				}
				tmp_eq = tmp_eq->next_equal;
			}
			if(flag) break;
		}
		if(!flag && tmp->operator_out){
			tmp = tmp->operator_out->output_value;
			if(!strcmp(tmp->name,varsearch->name)){
				op_ret = tmp->operator_out;
				flag=true;
				break;
			}
			else flag = false;
		}
		if(!flag && tmp->dfgnode_out){
			tmp = tmp->dfgnode_out->output;
			//after sending dfg_ret back,check dfg_ret->condition_op->equal_cond->lhs_value n send it back to this function
			if(!strcmp(tmp->name , varsearch->name)){
				dfg_ret = tmp->dfgnode_out;
				flag=true;
				break;
			}
			else flag=false;
		}
		if(!flag && tmp->comparator_out){
			tmpcomp = tmp->comparator_out;
			while(tmpcomp){
				tmp = tmpcomp->value_out;
				if(!strcmp(tmp->name,varsearch->name)){
					comp_ret = tmpcomp;
					flag = true;
					break;
				}
				else if(Search_back_node(varsearch,tmp,NULL,tmp_state,place_ret,tran_ret,equal_ret,op_ret,comp_ret,dfg_ret,signal_ret)){
					flag = true;
					break;
				}
				tmpcomp = tmpcomp->next_comparator;
			}
		}
		if(!flag && tmp->signal_selector_out){
			tmpsig = tmp->signal_selector_out;
			while(tmpsig){
				tmp = tmpsig->out_signal;
				if(!strcmp(tmp->name,varsearch->name)){
					signal_ret = tmpsig;
					flag=true;
					break;
				}
				else if(Search_back_node(varsearch,tmp,NULL,tmp_state,place_ret,tran_ret,equal_ret,op_ret,comp_ret,dfg_ret,signal_ret)){
					flag=true;
					break;
				}
				tmpsig = tmpsig->next_selector;
			}
			if(flag) break;
		}
		else tmp=NULL;
	}
	if(flag) break;
	
	if(!state)
		tmp_state = tmp_state->next_state;
	else tmp_state = NULL;
}

return flag;

}

//if control_st not having a state is sent, then the startnode must be traced back to the set of states and the node must be traced depthwise and checked for the same state while going depthwise

//function to insert the path from startnode TO the node until the state is control_st->state_node or control_st

//startnode is a node from petrigraph
//assumed datablock is created already
//endnode_attach is sent only when the endnode is known beforehand, which maybe the tail of a path already implmeneted in DFGgraph. endnode value is stored in this
//here the dataflow loop will also be checked for inserting the path from the exitnodes from the dataflow loop

void Insert_path_in_BasicBlock(Control_block *control_st,Basic_block *datablock, DeclareData *startnode,State_var *first_state,DeclareData *endnode_attach,bool loop_nodesend){

DeclareData *temp=NULL;
DeclareData *depth_tmp=NULL;
DeclareData *tmpdata=NULL;
DeclareData *tmpvar = NULL , *temp_var = NULL;
DeclareData *node_empty=NULL , *prev_var = NULL;
Equal_to_op *tmpeq=NULL , *eq_temp = NULL , *eq_node = NULL;
Compare_operator *prev_comp=NULL;
Signal_selector *prev_signal=NULL;
State_var *tmpst = NULL;
State_var *state_ret=NULL;
State_var *state_list[10];
int num=0;
Control_block *prev_control = NULL;
Control_block *tmp_control = NULL;
Control_block *control_create=NULL;
Control_block *control_ret = NULL;
Basic_block *block_ret=NULL , *block_null = NULL , *block_ret_tmp = NULL;
DeclareData *endnode=NULL , *endnode_tmp = NULL;
DeclareData *firstnode = NULL , *endnode_out = NULL;
Control_block *controlnode=NULL , *controlnode_tmp = NULL;
Control_block *loopcontrol = NULL;
Operate_op *tmpop = NULL , *prevop = NULL;
Path_list *tmp_exit = NULL;
Path_list *nodecheck = NULL;
Path_list *loopempty=NULL;
Path_list *header = NULL;
Place_block *tmp_place=NULL;
Condition_block *tmp_cond=NULL;
bool node_down=false;
bool loopflag = true;
bool stateflag=false;
bool loop_created = false;
bool state_check=false;
DeclareData *array_ptr[10];
bool dataflow_check = false;
bool input_var = false;
int i=0;

if(loop_nodesend){
	nodecheck = new Path_list;
	Initialize_array_pointer(nodecheck);
}


//in case, control_st doesnt contain state_name, then trace back startnode to obtain the set of states it was generated in, n then
else if(!loop_nodesend){
	if(!control_st->state_node){
		if(Trace_back_node(startnode, state_ret,first_state,NULL,state_list,true,true,NULL,true))
			state_check = true;
	}
	else{
		state_ret = control_st->state_node;
		state_check = false;
	}
}

//WHY TO HAVE A NESTED LOOP WITH TEMP.???? NEED TO DO EVERY BRANCH OF THE DEPTH_TMP DEPTHWISE
depth_tmp = startnode;

//do{
	if(depth_tmp->data_type == input){
		tmpdata = new DeclareData;
		assign_value(tmpdata,depth_tmp);
		input_var = true;
		if(!datablock->first_block_input)
			datablock->first_block_input = tmpdata;
		else Insert_var_list(datablock->first_block_input,tmpdata);
		if(!program_inputs)
			program_inputs = tmpdata;
		else Insert_var_list(program_inputs,tmpdata);
	}
	
		
	//depth_tmp = temp;
	while(depth_tmp){
		node_down=false;
		endnode = NULL;controlnode = NULL;endnode_attach = NULL;block_ret = NULL; endnode_tmp = NULL;tmpeq = NULL;temp_var = NULL;
		//here first check if path from depth_tmp is a dataflow loop. if yes,loop_created will be false(its only for controlflow loop) n dataflow_check will be true and exit_points will be returned back here. the fn returned shud be true
		//loop_nodesend is to indicate if this function isbeing called to insert the path of exit nodes of a loop. thismeans loop has been implemented
		//only if control_st exists, then, must check for loop_body
		if(!loop_nodesend && control_st  && Check_loop_body(depth_tmp,first_state,loop_created,dataflow_check,tmp_exit,false,firstnode,loopcontrol,true,header,false,tmp_place,NULL,control_st) && dataflow_check && tmp_exit){
	
			node_down = true;
			if(loopcontrol)
				datablock = loopcontrol->bb_ptr;
				
			while(tmp_exit){
				 if(tmp_exit->placenode)
				 	tmpvar = tmp_exit->placenode->first_trans_node->data_node->condition_op->assign_expr->rhs_value;
				 	
				 else if(tmp_exit->trannode)
				 	tmpvar = tmp_exit->trannode->data_node->assignment_graph->rhs_value;
				 
				 else if(tmp_exit->opnode){
				 	//find the input which is part of the loop, and send that input back to thisfunction as depth_tmp
				 	if(Search_back_petri_model(tmp_exit->opnode->op1,NULL,true,true,first_state,i,false,loopempty,false,array_ptr,10,false,block_ret,false,node_empty))
				 		tmpvar = tmp_exit->opnode->op1;
				 	else
				 		tmpvar = tmp_exit->opnode->op2;	
				 }
				 else if(tmp_exit->eqnode)
				 	tmpvar = tmp_exit->eqnode->rhs_value;
				
				 loop_nodesend = true;
				 Insert_path_in_BasicBlock(control_st,datablock,tmpvar,first_state,endnode_attach,true);
				 tmp_exit = tmp_exit->next_node;	
			}
			if(loop_nodesend){
				delete_loop_list();
				break;
			}
		}
		
		if(!node_down && depth_tmp->operator_out){
			if(loop_nodesend){
				nodecheck->opnode = depth_tmp->operator_out;
				if(!Search_path_list(nodecheck,NULL,NULL,NULL,depth_tmp->operator_out,NULL,NULL,NULL))
					loopflag = false;
			}
			//here we also need to check if the other operand of this operator is generated in control_st->state_node and its not part of a loop->loop_nodesend is F
			if(!loop_nodesend || !loopflag){
				tmpvar = depth_tmp;
				while(tmpvar){
					if( Search_state_of_OperatorInput(control_st,depth_tmp->operator_out,tmpvar,first_state,NULL,control_ret) && Search_end_node_BasicBlock(tmpvar , first_basic_block , endnode,controlnode,true, block_ret,false,NULL)){
					
						if(!controlnode) controlnode = control_st;

						if(block_ret == controlnode->bb_ptr)
							Create_subnodes_under_endnode(endnode , tmpvar,controlnode,block_ret,NULL,block_null,tmpeq,NULL,tmpop,depth_tmp->operator_out,true, 'a');
						else
							Create_subnodes_under_endnode(endnode , tmpvar,controlnode,controlnode->bb_ptr,NULL,block_ret,tmpeq,NULL,tmpop,depth_tmp->operator_out,true, 'a');
							
						
						if(!controlnode->bb_ptr) controlnode->bb_ptr = block_ret;
						//no need to add the input/output for control_ret,since control_ret is the other input's control block,and has not been checked if the other input has been created in DFG
						
						
						endnode=NULL;
					//	*temp = *depth_tmp;
						node_down=true;
					
					}
					if(tmpvar == depth_tmp->operator_out->op1)
						tmpvar = depth_tmp->operator_out->op2;
					else tmpvar=NULL;
				}
				if(node_down) depth_tmp = depth_tmp->operator_out->output_value;
			}
		}
		if(!node_down && depth_tmp->equal_op_out){
			eq_node = depth_tmp->equal_op_out;
			while(eq_node){
				if(loop_nodesend){
					nodecheck->eqnode = eq_node;
					if(!Search_path_list(nodecheck,NULL,NULL,eq_node,NULL,NULL,NULL,NULL))
						loopflag = false;
				}
				endnode = NULL; controlnode = NULL; endnode_out = NULL;block_ret_tmp = NULL;
				if(!loop_nodesend || !loopflag){
					if(depth_tmp->data_type==input || Search_end_node_BasicBlock(depth_tmp,first_basic_block,endnode,controlnode,true,block_ret,false,NULL)){
					
						if(depth_tmp->data_type == input)
							endnode = tmpdata;
						else if(endnode_attach) endnode = endnode_attach;
						
						if(!controlnode) controlnode = control_st;
						
						if(loop_nodesend && Search_end_node_BasicBlock(eq_node->lhs_value,first_basic_block,endnode_out,controlnode,true,block_ret_tmp,false,NULL)){
							if(block_ret == block_ret_tmp)
								Create_subnodes_under_endnode(endnode,depth_tmp , controlnode , block_ret ,NULL,block_null,tmpeq,eq_node,tmpop,NULL,false, 'b');
							else
								Create_subnodes_under_endnode(endnode,depth_tmp , controlnode , block_ret ,NULL,block_ret_tmp,tmpeq,eq_node,tmpop,NULL,false, 'b');
							tmpeq->lhs_value = endnode_out;
						}
						// since this is equal_op_out part, no controlnode is required as the equal node is to be attached simply wherever the endnode is
						else if(block_ret == controlnode->bb_ptr)
							Create_subnodes_under_endnode(endnode,depth_tmp , controlnode , block_ret ,NULL,block_null,tmpeq,eq_node,tmpop,NULL,true, 'b');
						else
							Create_subnodes_under_endnode(endnode,depth_tmp , controlnode , controlnode->bb_ptr,NULL,block_ret,tmpeq,eq_node,tmpop,NULL,true, 'b');	
						endnode_attach=NULL;
						if(!endnode_out)
							Insert_path_in_BasicBlock(control_st,datablock,eq_node->lhs_value,first_state,NULL,loop_nodesend);
						
						//in this case, node_down will remain false
					}
					else node_down = false;
				}
				 eq_node = eq_node->next_equal;
				//else eq_node = NULL;
			}
		}
		//if the output of this place is connected to a comparator or signal selector, then connect this place also as a control node
		//RULE 7
		if(!node_down && depth_tmp->place_ptr){
			tmp_place = depth_tmp->place_ptr;
		
			while(tmp_place && Search_var_in_InputList(depth_tmp,tmp_place,NULL)){
				if(loop_nodesend){
					nodecheck->placenode = tmp_place;
					if(Search_path_list(nodecheck,tmp_place,NULL,NULL,NULL,NULL,NULL,NULL)){
						tmp_place = tmp_place->next_place;
						continue;
					}
					
				}
				tmpvar = tmp_place->state_place_input;
				stateflag=false;
				while(tmpvar){
					if(!loop_nodesend){
						if((state_check && Search_state_in_list(NULL,tmpvar,state_list,10)) || (!state_check && !strcmp(tmpvar->name,state_ret->state_name->name))){
							stateflag=true;
							break;
						}
					}
					else if(loop_nodesend){
						//the tmpst should be searched for the control node accordingly, and that control node should be associated with the current datablock
						if(Search_var_from_statelist(tmpvar,tmpst,false) && Search_state_from_controlnode_list(tmpst,first_control_node,prev_control)){
							if(prev_control == control_st)
								prev_control = NULL;
							stateflag = true;
							break;
						}
					}
					else tmpvar = tmpvar->next_n;
				}
				if(!stateflag && !tmp_place->state_place_input){
					temp = tmp_place->first_place_input;
					if(tmp_place->first_trans_node->data_node->assignment_graph)
						temp_var = tmp_place->first_trans_node->data_node->assignment_graph->rhs_value;
					else{
						 temp_var = tmp_place->first_trans_node->data_node->condition_op->assign_expr->rhs_value;
						 if(tmp_place->first_trans_node->data_node->condition_op->equal_cond)
						 	eq_temp = tmp_place->first_trans_node->data_node->condition_op->equal_cond;
					}
					while(temp){
						if(strcmp(temp->name ,temp_var->name)){
							if(temp->unary_operator||Search_var_from_graph(temp,NULL,NULL,prev_comp,prev_signal,prevop,prev_var,first_state,false,true)){
								if(Search_control_nodes(NULL, controlnode ,node_empty, temp,NULL)){
							
									endnode_tmp = node_empty; 
								
									stateflag=true;
									break;
								}	
								
							}
							else if(!loop_nodesend && Trace_back_node(temp , tmpst,first_state,NULL,state_list,true,false,NULL,true) && !strcmp(tmpst->state_name->name , control_st->state_node->state_name->name)){
								stateflag = true;
								break;
							}
						}
						else if(eq_temp && !strcmp(temp->name,eq_temp->lhs_value->name) && Search_end_node_BasicBlock(temp, first_basic_block ,endnode,controlnode_tmp,true, block_ret,false,NULL)){
								Create_control_node(tmp_control,endnode,NULL,control_st,first_state,controlnode,NULL,tmp_place->first_trans_node->data_node->condition_op,NULL,false);
								stateflag = true;	
								break;
							
						}
							
						if(!stateflag) temp = temp->next_n;
					}
				}
				if(stateflag){
					endnode = NULL;controlnode = NULL; endnode_out = NULL;
					if(depth_tmp->data_type == input || Search_end_node_BasicBlock(depth_tmp , first_basic_block ,endnode,controlnode,true, block_ret,false,NULL)){
						if(depth_tmp->data_type == input)
							endnode = tmpdata;
							
						if(loop_nodesend && Search_end_node_BasicBlock(tmp_place->first_trans_node->output_var,first_basic_block,endnode_out,controlnode,true,block_ret_tmp,false,NULL)){
							if(block_ret_tmp == block_ret)
								Create_subnodes_under_endnode(endnode,depth_tmp ,controlnode,block_ret ,tmp_place,block_null,tmpeq,NULL,tmpop,NULL,false, 'p');
							else 
								Create_subnodes_under_endnode(endnode ,depth_tmp ,controlnode,block_ret ,tmp_place,block_ret_tmp,tmpeq,NULL,tmpop,NULL,false, 'p');
								tmpeq->lhs_value = endnode_out;
						}
						//EDITING TO DO HERE! Call Search_BasicBlock_from_control_list
						else if(block_ret == control_st->bb_ptr)
							Create_subnodes_under_endnode(endnode ,depth_tmp ,controlnode,block_ret ,tmp_place,block_null,tmpeq,NULL,tmpop,NULL,true, 'p');
						else
							Create_subnodes_under_endnode(endnode ,depth_tmp ,controlnode,datablock ,tmp_place,block_ret,tmpeq,NULL,tmpop,NULL,true, 'p');
						//node_down = true;
						if(prev_control)
							Insert_in_BasicBlock_array(block_ret,10,prev_control);
							
						if(endnode_tmp){
							if(!endnode_tmp->equal_op_out) endnode_tmp->equal_op_out = tmpeq;
							else Insert_in_equalto_list(NULL,endnode_tmp,tmpeq);
						}
						else if(tmp_control){
							if( !tmp_control->bb_ptr) tmp_control->bb_ptr = block_ret;
							Insert_in_BasicBlock_array(block_ret,10,tmp_control);
						}
						if(!endnode_out)
							//the depth_tmp is depthwise created.only when the output of the place is not already created
							Insert_path_in_BasicBlock(control_st,datablock,tmp_place->first_trans_node->output_var,first_state,NULL,loop_nodesend);
						//in this case, depth_tmp will remain false.
					}
				}
				tmp_place = tmp_place->next_place;
				//else tmp_place=NULL;
			} 
		}
		if(!node_down && depth_tmp->transition_out){
			if(loop_nodesend){
				nodecheck->trannode = depth_tmp->transition_out;
				if(!Search_path_list(nodecheck,NULL,depth_tmp->transition_out,NULL,NULL,NULL,NULL,NULL))
					loopflag = false;
			}
			if(!loop_nodesend || !loopflag){
				if(Search_end_node_BasicBlock(depth_tmp , datablock , endnode,controlnode,false,block_ret,false,NULL)||(datablock->prev_block && Search_end_node_BasicBlock(depth_tmp , first_basic_block ,endnode,controlnode,true, block_ret,false,NULL))){
					 Create_subnodes_under_endnode(endnode,depth_tmp,controlnode,datablock ,NULL,block_ret,tmpeq,depth_tmp->transition_out->data_node->assignment_graph,tmpop,NULL,true, 't');
					node_down = true;
					//*temp = *depth_tmp;
					depth_tmp = depth_tmp->transition_out->output_var;
				
				}	
				else node_down=false;
			}
		}
		if(!node_down && depth_tmp->comparator_out){
			Search_comp_SS_path_subfunction(loop_nodesend,node_down,depth_tmp,nodecheck,datablock,first_state,control_st,state_check,state_list,state_ret);
		}
		if(!node_down && depth_tmp->signal_selector_out){
			Search_comp_SS_path_subfunction(loop_nodesend,node_down,depth_tmp,nodecheck,datablock,first_state,control_st,state_check,state_list,state_ret);
		}
		//CUT HERE
		//put the case for switch-case depth_tmp->dfgnode_out this contains cond_op
		if(!node_down && depth_tmp->dfgnode_out){
			if(loop_nodesend){
				nodecheck->dfgnode = depth_tmp->dfgnode_out;
				if(!Search_path_list(nodecheck,NULL,NULL,NULL,NULL,depth_tmp->dfgnode_out,NULL,NULL))
					loopflag = false;
			}
			if(!loop_nodesend || !loopflag){
				tmp_cond = depth_tmp->dfgnode_out->condition_op;
				//firstnode contains the rhs_value of the  condition of the dfgnode
				
				while(tmp_cond){
					firstnode = tmp_cond->assign_expr->rhs_value;
					endnode = NULL;controlnode = NULL;block_ret = NULL;
					if(Search_end_node_BasicBlock(firstnode,first_basic_block,endnode,controlnode,true,block_ret,false,NULL)){
						
						Create_nodes_for_conditional_block(firstnode,tmp_cond,first_state,control_st,control_create,datablock);
						node_down = true;			
					}
						
					tmp_cond = tmp_cond->next_cond;
				
				}
				depth_tmp = depth_tmp->dfgnode_out->output;
			}
			
		}
		if(node_down && depth_tmp->data_type == output){
			if(!datablock->first_block_output) datablock->first_block_output = endnode;
			else Insert_in_node_list(datablock->first_block_output,endnode);
		}
		if(!node_down) depth_tmp = NULL;
	}			
	
//}while(temp && !loop_nodesend);


if(loop_nodesend){
	delete nodecheck;
	nodecheck=NULL;
}


}


//fn is a sub-part of Insert_path_BasicBlock for creating paths if the variable has comparator_out or signal_selector_out
void Search_comp_SS_path_subfunction(bool& loop_nodesend,bool& node_down,DeclareData *depth_tmp,Path_list*& nodecheck,Basic_block *datablock,State_var *first_state,Control_block *control_st,bool state_check,State_var** state_list,State_var *state_ret){

bool stateflag=false;
Compare_operator *tmp_comp = NULL;
State_var *tmpst = NULL;
DeclareData *tmpdata = NULL;
DeclareData *endnode = NULL;
Control_block *controlnode=NULL;
Control_block *tmp_control=NULL;
Basic_block *block_ret = NULL;
Signal_selector *tmp_signal = NULL;
DeclareData *tmp = NULL;


if(depth_tmp->comparator_out){
			if(loop_nodesend){
				nodecheck->compnode = depth_tmp->comparator_out;
				if(!Search_path_list(nodecheck,NULL,NULL,NULL,NULL,NULL,depth_tmp->comparator_out,NULL))
					loop_nodesend = false;
			}
			if(!loop_nodesend){
				stateflag = false;
				tmp_comp = depth_tmp->comparator_out;
				while(tmp_comp){
					tmpst = tmp_comp->state_condition;
					if(tmpst && (state_check && Search_state_in_list(tmpst,NULL,state_list,10)) || (!state_check && !strcmp(tmpst->state_name->name,state_ret->state_name->name))) 	
						stateflag = true;	
					if(!stateflag && !tmpst){
						tmpdata = tmp_comp->condition_value;
						
						if(Trace_back_node(tmpdata , tmpst,first_state,NULL,state_list,true,false,NULL,true) && control_st->state_node && !strcmp(tmpst->state_name->name , control_st->state_node->state_name->name))
							stateflag= true;
					}
					if(stateflag){
						
						if( Search_end_node_BasicBlock(depth_tmp , datablock , endnode,controlnode,false,block_ret,false,NULL)||(datablock->prev_block && Search_end_node_BasicBlock(depth_tmp , first_basic_block ,endnode,controlnode,true, block_ret,false,NULL))){
							Create_control_node(tmp_control,endnode,tmp_comp,control_st,first_state,controlnode,NULL,NULL,NULL,false);
							depth_tmp = depth_tmp->comparator_out->value_out;
							node_down = true;
							//*temp = *depth_tmp;
							 if(block_ret){
								if(!block_ret->first_block_output) block_ret->first_block_output = endnode;
								else Insert_in_node_list(block_ret->first_block_output,endnode);
							}
							else{
								Insert_var_list(tmp_control->control_in_from_dfg , endnode);
								endnode->comparator_out = tmp_control->control_compare_node;
							}
						}
					}
					tmp_comp = tmp_comp->next_comparator;
				}
			}
				
}
		//signal_selector wont be a part of dataflow loop anyways ASSUMPTION
else if(depth_tmp->signal_selector_out){
			stateflag=false;
			tmp_signal = depth_tmp->signal_selector_out;
			while(tmp_signal){
				tmpdata = tmp_signal->state_in_signal;
				while(tmpdata){
					if( (state_check && Search_state_in_list(NULL,tmpdata,state_list,10)) || (!state_check && !strcmp(tmpdata->name , state_ret->state_name->name))){
						stateflag=true;
						break;
					}
					tmpdata = tmpdata->next_n;
				}
				if(!stateflag && !tmp_signal->state_in_signal){
					tmpdata = tmp_signal->in_signal_list;
					while(tmpdata){
						if(Trace_back_node(tmpdata , tmpst,first_state,NULL,state_list,true,false,NULL,true) && control_st->state_node && !strcmp(tmpst->state_name->name , control_st->state_node->state_name->name)){
							stateflag=true;
							break;
						}
						else tmpdata = tmpdata->next_n;
					}
				}
				if(stateflag){
					tmpdata = tmp_signal->in_signal_list;
					while(tmpdata){
						
						if(Search_end_node_BasicBlock(depth_tmp , datablock,endnode,controlnode,false,block_ret,false,NULL) || (datablock->prev_block && Search_end_node_BasicBlock(depth_tmp , first_basic_block ,endnode,controlnode,true, block_ret,false,NULL))){
							node_down = true;
							if(tmpdata == tmp_signal->in_signal_list){
								
								Create_control_node(tmp_control,endnode , NULL,control_st,first_state,controlnode,tmp_signal,NULL,NULL,false);
							}
							else{
								if(tmp_control->signal_select_node->in_signal_list) tmp_control->signal_select_node->in_signal_list=endnode;
								Insert_in_node_list(tmp_control->signal_select_node->in_signal_list,endnode);
							}
							//in this case, block_ret wil have the datablock where endnode is found, in previous datablocks
							 if(block_ret){
								if(!block_ret->first_block_output) block_ret->first_block_output = endnode;
								else Insert_in_node_list(block_ret->first_block_output,endnode);
							 }
							// for the rest of the signals
							else{
								Insert_var_list(tmp_control->control_in_from_dfg , endnode);
								endnode->signal_selector_out = tmp_control->signal_select_node;
							}
						}
						
						tmpdata = tmpdata->next_n;
					}
					if(node_down) depth_tmp = depth_tmp->signal_selector_out->out_signal;
					//*temp = *depth_tmp;
				}
				tmp_signal = tmp_signal->next_selector;
			}
		
		}


}


//fn to search a basic_block from the list of control nodes
bool Search_BasicBlock_from_control_list(Basic_block *searchblock, Control_block *first_control_node,Control_block*& control_ret){

bool search = false;
Control_block *tmpnode = NULL;
Control_block *tmp = NULL;
tmpnode = first_control_node;

while(tmpnode){
	if(tmpnode->bb_ptr && tmpnode->bb_ptr == searchblock){
		search = true;
		control_ret = tmpnode;
		break;
	}
	else if(tmpnode->result_control){
		tmp = tmpnode->result_control;
		while(tmp){
			if(Search_BasicBlock_from_control_list(searchblock,tmp,control_ret)){
				search = true;
				break;
			}
			tmp = tmp->next_control_block;
		}
		if(search) break;
	}
	tmpnode = tmpnode->next_control_block;
}

return search;
}






//function to create the appropriate nodes for the conditional node(switch-case block)
//depth_node is the node from petrigraph - the control variable for the switchcase
//control_create is the controlblock newly made to show the equal condition in switchcase
//control_node will contain the control_Block in which condition_var was generatd.so it can be used when the depth_nod is input type. the basicblock of this control_node willhave the creation of equalnode in this case
void Create_nodes_for_conditional_block(DeclareData *depth_node, Condition_block *tmp_cond, State_var *first_state,Control_block*& control_prev , Control_block*& control_create,Basic_block*& block_prev){

//Control_block *control_create=NULL;
Equal_to_op *tmpeq=NULL;
Operate_op *tmpop=NULL;
Basic_block *block=NULL;
DeclareData *var=NULL;
DeclareData *condvar = NULL;
DeclareData *end_node = NULL;
Control_block *control_node = NULL;
Control_block *loopcontrol = NULL;
Basic_block *block_ret = NULL;
bool loop_created = false;
bool loop_dataflow = false;
bool condition_found = false;
Path_list *tmp_exit = NULL , *node_null = NULL;
Place_block *placenull = NULL;

condvar = tmp_cond->equal_cond->lhs_value;

//this part is for creating the control node having comparator and attaching the condition_var
if(Search_end_node_BasicBlock(condvar, first_basic_block ,end_node,control_node,true, block_ret,false,NULL)){
	
		Create_control_node(control_create , end_node,NULL,control_node,first_state,control_prev,NULL,tmp_cond,NULL,false);
		if(Search_BasicBlock_from_control_list(block_ret,first_control_node,control_node)){
			control_prev = control_node;
			condition_found = true;
		}
		control_create->control_in_from_dfg = end_node;
		
	}
	else if(Search_control_nodes(NULL, control_node,end_node,condvar,NULL)){
		Create_control_node(control_create,end_node,NULL,control_node,first_state,control_prev,NULL,tmp_cond,NULL,false);
		control_create->control_in = control_prev;
		control_prev = control_node;
		if(control_node->bb_ptr) block_prev = control_node->bb_ptr;
		else{
			control_node->bb_ptr = new Basic_block;
			Initialize_nodes(NULL,NULL,NULL,NULL,control_node->bb_ptr,NULL);
			block_prev = control_node->bb_ptr;			
		}
		condition_found = true;
	}
	else if(Check_loop_body(condvar,first_state,loop_created,loop_dataflow,tmp_exit,false,end_node,loopcontrol,true,node_null,false,placenull,NULL,control_prev)){
		if(loopcontrol)
			Create_control_node(control_create,end_node,NULL, loopcontrol,first_state,control_prev,NULL,tmp_cond,NULL,false);
		condition_found = true;
		control_node = loopcontrol;
		control_prev = loopcontrol;
		block_prev = loopcontrol->bb_ptr;
	}
		
	//depth_node is the rhs_value of the dfgnode->condition_op->assign_expr
	
	//here control_node is the parent control node of control_create. That is why it is being used for 
	
//this is the part for the other cases of the switch-case node, attaching the equal nodes in parallel
 if( condition_found && (Search_end_node_BasicBlock(depth_node, first_basic_block ,end_node,control_node,true, block_ret,false,NULL) || Check_parent_nodes(depth_node,first_state,NULL,control_node,end_node,block_ret))){

	//control_node for the case when Check_parentnodes fn is active will be the control_block where similar depth_node is already inserted
	//control_node is not obtained from the Search_endnode() function.
		if(control_node && block_ret == control_node->bb_ptr){
			//block is NULL here
			Create_subnodes_under_endnode(end_node,depth_node, control_node , block_ret,NULL,block,tmpeq,tmp_cond->assign_expr,tmpop,NULL,false, 'b');	
			block = block_ret;
		}
		else if(control_node){
			Create_subnodes_under_endnode(end_node,depth_node, control_node ,control_node->bb_ptr,NULL,block_ret,tmpeq,tmp_cond->assign_expr,tmpop,NULL,false, 'b');
			block = control_node->bb_ptr;
		}
		else Create_subnodes_under_endnode(end_node,depth_node, control_node ,block,NULL,block_ret,tmpeq,tmp_cond->assign_expr,tmpop,NULL,false, 'b');
		/*
		if(Search_end_node_BasicBlock(tmp_cond->assign_expr->lhs_value,first_basic_block ,end_node,control_node,true, block_ret,false,NULL))
			tmpeq->lhs_value = end_node;
		else{
			tmpeq->lhs_value = new DeclareData;
			assign_value(tmpeq->lhs_value,tmp_cond->assign_expr->lhs_value);
		}*/
		
		if(!control_create->control_out){
			control_create->control_out = new DeclareData;
			Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,control_create->control_out,NULL,NULL,NULL);
			control_create->control_out->equal_op_out = tmpeq;
		}
		if(!control_create->bb_ptr) control_create->bb_ptr = block_ret;
		if(control_node && !control_node->result_control) control_node->result_control = control_create;
		else Insert_in_child_list(control_node->result_control,control_create);
}

//if data_type of the depth_node is input, this means it wont be available in any basic_block and the node has to be inserted in the basic block of control_block where tmpcond->if_cond_var is generated
else if(condition_found && depth_node->data_type==input){
//insert it as a block input first
	block = control_node->bb_ptr;
	var = new DeclareData;
	 assign_value(var, depth_node);
	if(!block->first_block_input){
		 block->first_block_input = var;
		 block->first_block_input->next_n = NULL;
	}
	else Insert_var_list(block->first_block_input , var);
	
	//end_node = var;
	//then create the equal node from the input datanode,
	var->equal_op_out = new Equal_to_op;
	Initialize_structures(NULL, NULL,NULL,NULL,var->equal_op_out,NULL);
	var->equal_op_out->rhs_value = var;
	var->equal_op_out->lhs_value = new DeclareData;
	assign_value(var->equal_op_out->lhs_value,tmp_cond->assign_expr->lhs_value);
	
	if(!control_create->bb_ptr) control_create->bb_ptr = block;
	if(!control_node->result_control) control_node->result_control = control_create;
	else Insert_in_child_list(control_node->result_control,control_create);
	
}

}



//this function is for creating a particular control node if the output is from compare_operator / SS (from petrigraph)
//flag is for indicating if tmp_comp or tmp_signal is the generator of endnode in petri-graph, then eq_attach is the dfg_node of the place which is transformed to a new control node and attached under endnode & control_attach
void Create_control_node(Control_block*& tmp_control,DeclareData*& endnode,Compare_operator *tmp_comp,Control_block*& control_st,State_var *first_state,Control_block*& control_attach,Signal_selector *tmp_signal,Condition_block *tmpcond,Equal_to_op *eq_attach,bool flag){


Control_block *control_ret=NULL;
DeclareData *node_ret=NULL;
Control_block *prev_control=NULL;
bool node_down=false;

tmp_control = new Control_block;
Initialize_nodes(NULL,NULL,NULL,tmp_control,NULL,NULL);
//if(!endnode){
	//endnode = new DeclareData;
	//Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,endnode,NULL,NULL,NULL);
//}

if(tmp_comp){

	if(flag){
		tmp_control->eq_node = new Equal_to_op;
		Initialize_structures(NULL,NULL,NULL,NULL,tmp_control->eq_node,NULL);
		tmp_control->eq_node->rhs_value = endnode;
		tmp_control->eq_node->lhs_value = new DeclareData;
		assign_value(tmp_control->eq_node->lhs_value , eq_attach->lhs_value);
		if(endnode)
			endnode->equal_op_out = tmp_control->eq_node;
	}
	else{
		
		tmp_control->control_compare_node = new Compare_operator;
		Initialize_nodes(NULL,tmp_control->control_compare_node,NULL,NULL,NULL,NULL);
		tmp_control->control_compare_node->lhs_compare = endnode;
		tmp_control->control_compare_node->opsymbol = tmp_comp->opsymbol;
		tmp_control->control_compare_node->value_compare = tmp_comp->value_compare;
		tmp_control->control_out = new DeclareData;
		assign_value(tmp_control->control_out , tmp_comp->value_out);
		tmp_control->control_compare_node->value_out = tmp_control->control_out;
		if(endnode){
			if(!endnode->comparator_out) endnode->comparator_out = tmp_control->control_compare_node;
			else insert_in_operator_list(endnode , NULL,NULL,false,tmp_control->control_compare_node,true);
		}
		//tmp_control->control_in_from_dfg = endnode;				
		node_down=true;
							//either comparator->state_condition or comparator->condition_value one of them will b valid
							//this part only for state_condition
		if(tmp_comp->state_condition && control_st){
			if(control_st->state_node && !strcmp(tmp_comp->state_condition->state_name->name , control_st->state_node->state_name->name)){
			
				if(!control_st->result_control) control_st->result_control = tmp_control;
				
				else Insert_in_child_list(control_st->result_control , tmp_control);
				//if(!tmp_control->control_in) tmp_control->control_in = control_st;
				//else Insert_in_child_list(tmp_control->control_in, control_st);
									
			}
			else if(Search_state_from_controlnode_list(tmp_comp->state_condition , first_control_node,prev_control)){
				if(!prev_control->result_control) 
					prev_control->result_control = tmp_control;
				else 
					Insert_in_child_list(prev_control->result_control, tmp_control);
				//if(!tmp_control->control_in) 
				//	tmp_control->control_in = prev_control;
				//else 
				//	Insert_in_child_list(tmp_control->control_in , prev_control);
									
			}
									
		}
							// this part for if there is condition_value instead of state_condition(ifcondition_var)
		else if(tmp_comp->condition_value){
								//this is an ifcondition_var, thus this can be only a wire, and is traced only in control blocks
			
			if(Search_control_nodes(NULL , control_ret,node_ret,tmp_comp->condition_value,NULL)){
								//assuming this function finds the control_ret whose output is the same as tmop_comp->condition_Value
				if(!control_ret->result_control) control_ret->result_control = tmp_control;
				else Insert_in_child_list(control_ret->result_control,tmp_control);
									//attach the comparator from the prev_control's control_out
				control_ret->control_out = node_ret;
				node_ret->comparator_out = tmp_control->control_compare_node;
				if(!control_ret->control_out->comparator_out) 
					control_ret->control_out->comparator_out = tmp_control->control_compare_node;
				else 
					insert_in_operator_list(control_ret->control_out , NULL,NULL,false,tmp_control->control_compare_node,true);
			}
		}
	}
	if(control_attach){
		if(!control_attach->control_out) control_attach->control_out = endnode;
		else control_attach->control_out->comparator_out = tmp_control->control_compare_node;
		//if(!tmp_control->control_in) tmp_control->control_in = control_attach;
		//else Insert_in_child_list(tmp_control->control_in,control_attach);
		if(!control_attach->result_control) control_attach->result_control = tmp_control;
		else Insert_in_control_list(control_attach->result_control,tmp_control);
	}
}
else if(tmp_signal){
	
	if(flag){
		tmp_control->eq_node = new Equal_to_op;
		Initialize_structures(NULL,NULL,NULL,NULL,tmp_control->eq_node,NULL);
		tmp_control->eq_node->rhs_value = endnode;
		tmp_control->eq_node->lhs_value = new DeclareData;
		assign_value(tmp_control->eq_node->lhs_value , eq_attach->lhs_value);
		endnode->equal_op_out = tmp_control->eq_node;
		
	}
	else{
		
		tmp_control->signal_select_node = new Signal_selector;
		Initialize_nodes(tmp_control->signal_select_node,NULL,NULL,NULL,NULL,NULL);
		tmp_control->signal_select_node->out_signal = new DeclareData;
		assign_value(tmp_control->signal_select_node->out_signal, tmp_signal->out_signal);
		//if(tmp_signal->state_in_signal){
		//	if(!tmp_control->signal_select_node->state_in_signal) tmp_control->signal_select_node->state_in_signal = endnode;
		//	else Insert_var_list(tmp_control->signal_select_node->state_in_signal,endnode);
		//}
		if(endnode){
			tmp_control->control_in_from_dfg = endnode;
			tmp_control->signal_select_node->in_signal_list = endnode;
			endnode->signal_selector_out = tmp_control->signal_select_node;
		}
			
		if(control_st){
			if(!control_st->result_control) control_st->result_control = tmp_control;
			else Insert_in_child_list(control_st->result_control , tmp_control);
			//if(!tmp_control->control_in) tmp_control->control_in = control_st;
			//else Insert_in_child_list(tmp_control->control_in, control_st);
		}
	}
	if(control_attach){
		control_attach->control_out = endnode;
		if(!control_attach->result_control) control_attach->result_control = tmp_control;
		else Insert_in_control_list(control_attach->result_control,tmp_control);
		//if(!tmp_control->control_in) tmp_control->control_in = control_attach;
		//else Insert_in_child_list(tmp_control->control_in,control_attach);
		
		if(tmp_signal->state_in_signal && control_attach->state_node){
			tmp_control->signal_select_node->state_in_signal = control_attach->state_node->state_name;
		}
	}
}

else if(tmpcond){
	
	
	tmp_control->control_compare_node = new Compare_operator;
	Initialize_nodes(NULL,tmp_control->control_compare_node,NULL,NULL,NULL,NULL);
	tmp_control->control_compare_node->lhs_compare = endnode;
	tmp_control->control_compare_node->value_compare = tmpcond->equal_cond->rhs_value->name;
//	assign_value(tmp_control->control_compare_node->value_compare , tmpcond->equal_cond->rhs_value);
	tmp_control->control_compare_node->opsymbol = '=';
	
	if(!control_st->result_control) control_st->result_control = tmp_control;	
	else Insert_in_child_list(control_st->result_control , tmp_control);
	
	endnode->comparator_out = tmp_control->control_compare_node;
	//if(!tmp_control->control_in) tmp_control->control_in = control_st;
	//else Insert_in_child_list(tmp_control->control_in, control_st);
	if(control_attach){
		control_attach->control_out = endnode;
		//tmp_control->control_in = control_attach;
		if(!control_attach->result_control) control_attach->result_control = tmp_control;
		else Insert_in_control_list(control_attach->result_control,tmp_control);
	}
	

}						

}


//function to create different type of child node under the variable endnode
// if ur not sending depth_tmp, then the transition nodes must be sent through eq_create
void Create_subnodes_under_endnode( DeclareData*& endnode , DeclareData *depth_tmp , Control_block*& controlnode,Basic_block *datablock ,Place_block *tmp_place, Basic_block*& block_ret,Equal_to_op*& tmpeq,Equal_to_op *eq_create,Operate_op*& tmpop,Operate_op *op_create,bool lhsflag, char choice){

DeclareData *tmpnode = NULL;
Control_block *control_tmp = NULL;
Basic_block *blk = NULL;
bool opcreated = false;

switch(choice){
	case 'a':
	{
		//case for operator
		//in this case, both the inputs must be attached. but function is called only once.thus, check if the tmpop has been created, run this in while loop.
		//while(depth_tmp){
			if(depth_tmp == op_create->op1){
				if(endnode->operator_out){
					//tmpop = endnode->operator_out;
					endnode->operator_out->op1 = endnode;
					opcreated = true;
				}
				else{
					tmpop= new Operate_op;
					Initialize_structures(NULL, NULL,NULL,tmpop,NULL,NULL);
					tmpop->op1 = endnode;
					endnode->operator_out = tmpop;
					tmpop->op_type = op_create->op_type;
				}
				
			}
			else if(depth_tmp == op_create->op2){
				if(endnode->operator_out){
					//tmpop = endnode->operator_out;
					endnode->operator_out->op2 = endnode;
					opcreated = true;
				}
				else{
					tmpop= new Operate_op;
					Initialize_structures(NULL, NULL,NULL,tmpop,NULL,NULL);
					tmpop->op2 = endnode;
					endnode->operator_out = tmpop;
					tmpop->op_type = op_create->op_type;
				}
					
			}
				//tmpop->op2 = endnode;
				
		if(!opcreated){
			endnode->operator_out->output_value = new DeclareData;
			assign_value(endnode->operator_out->output_value,op_create->output_value);
		}
		if(controlnode){
			if(!controlnode->control_out) controlnode->control_out = endnode;
			if(!controlnode->bb_ptr) controlnode->bb_ptr = datablock;
			//else Insert_in_BasicBlock_list(controlnode , datablock);
			controlnode->control_out->operator_out = endnode->operator_out;
		}
		//if endnode is not found , and either search itfrom other datablocks if they exist, else create it as a first block input 
		else if(block_ret){
			if(!block_ret->first_block_output) block_ret->first_block_output = endnode;
			else Insert_in_node_list(block_ret->first_block_output,endnode);
			if(!datablock->first_block_input) datablock->first_block_input = endnode;
			else Insert_in_node_list(datablock->first_block_input,endnode);
		}
		break;
	}
	case 'b':
	{
		//this case is for equalop
		tmpeq = new Equal_to_op;
		Initialize_structures(NULL, NULL,NULL,NULL,tmpeq,NULL);
		tmpeq->rhs_value = endnode;
		if(lhsflag){
			tmpeq->lhs_value = new DeclareData;
			if(depth_tmp)
				 assign_value(tmpeq->lhs_value , depth_tmp->equal_op_out->lhs_value);
			else
				assign_value(tmpeq->lhs_value,eq_create->lhs_value);
		}
		else if(!lhsflag && Search_end_node_BasicBlock(eq_create->lhs_value,first_basic_block ,tmpnode,control_tmp,true, blk,false,NULL))
			tmpeq->lhs_value = tmpnode;
		else{
			tmpeq->lhs_value = new DeclareData;
			assign_value(tmpeq->lhs_value,eq_create->lhs_value);
		}
		tmpeq->opsymbol = eq_create->opsymbol;
		
		if(!endnode->equal_op_out) endnode->equal_op_out = tmpeq;
		else Insert_in_equalto_list(NULL,endnode , tmpeq);
		//this controlnode is sent only if this equalnode is created out of the conditional block.
		if(controlnode){
			if(!controlnode->bb_ptr) controlnode->bb_ptr = datablock;
			//else Insert_in_BasicBlock_list(controlnode , datablock);
			controlnode->control_out->equal_op_out = endnode->equal_op_out;
		}
		if(block_ret){
			if(!block_ret->first_block_output) block_ret->first_block_output = endnode;
			else Insert_in_node_list(block_ret->first_block_output,endnode);
			if(!datablock->first_block_input) datablock->first_block_input = endnode;
			else Insert_in_node_list(datablock->first_block_input,endnode);
		}
		break;
	}
	case 't':
	{
		//this case is for transitions
		tmpeq = new Equal_to_op;
		Initialize_structures(NULL, NULL,NULL,NULL,tmpeq,NULL);
		tmpeq->rhs_value = endnode;
		tmpeq->lhs_value = new DeclareData;
		tmpeq->opsymbol = '=';
		if(depth_tmp)
			assign_value(tmpeq->lhs_value , depth_tmp->transition_out->output_var);
		else 	assign_value(tmpeq->lhs_value , eq_create->lhs_value);
		if(!endnode->equal_op_out)  endnode->equal_op_out = tmpeq;
		 else Insert_in_equalto_list(NULL,endnode, tmpeq);
		 if(controlnode){
		 	controlnode->control_out = endnode;
			if(!controlnode->bb_ptr) controlnode->bb_ptr = datablock;
			//else Insert_in_BasicBlock_list(controlnode , datablock);
			controlnode->control_out->equal_op_out = tmpeq;
		}
		else if(block_ret){
			if(!block_ret->first_block_output) block_ret->first_block_output = endnode;
			else Insert_in_node_list(block_ret->first_block_output,endnode);
			if(!datablock->first_block_input) datablock->first_block_input = endnode;
			else Insert_in_node_list(datablock->first_block_input,endnode);
		}
		break;
	}
	case 'p':
	{
		//this case is for transforming place nodes
		tmpeq = new Equal_to_op;
		Initialize_structures(NULL, NULL,NULL,NULL,tmpeq,NULL);
		tmpeq->rhs_value = endnode;
		tmpeq->opsymbol = '=';
		if(lhsflag){
			tmpeq->lhs_value = new DeclareData;
			assign_value(tmpeq->lhs_value, tmp_place->first_trans_node->output_var);
		}
		if(!endnode->equal_op_out) endnode->equal_op_out = tmpeq;
		else Insert_in_equalto_list(NULL,endnode , tmpeq);
		if(controlnode){
			if(!controlnode->control_out) controlnode->control_out = endnode;
			if(!controlnode->bb_ptr) controlnode->bb_ptr = datablock;
			//else Insert_in_BasicBlock_list(controlnode , datablock);
		}
		else if(block_ret){
			if(!block_ret->first_block_output) block_ret->first_block_output = endnode;
			else Insert_in_node_list(block_ret->first_block_output,endnode);
			if(!datablock->first_block_input) datablock->first_block_input = endnode;
			else Insert_in_node_list(datablock->first_block_input,endnode);
		}
	}

}

}



//petrigraph search

//this function is to trace back vartosearch in order to find the state(ret_state) which generated it
//the flag state is to indicate if this function is called from outside(true), or called recursively inside(false)
//the state flag is also to indicate if the function should search all the children of only one state or all state nodes
//state true means search all states else search only state_continue
//the tmpvar is in the beginning a statevariable but it can be replaced by a normal variable, thus conditions are stated accordingly

//while tracing top-to-bottom, we only pursue the control flow inputs to the place, and not the dataflow inputs because, in that case, you have to check the state of the
//control flow inputs, which anyways will be checked during the outer while loop of the tmpstate
//send_all_states flag is for indicating that all the states attached to the place must be sent back
//if send_all_states flag is true, then the send the array of states via state_list, else send one state via ret_state
//flag is to indicate if fn is called internally or externally

bool Trace_back_node(DeclareData *vartosearch, State_var*& ret_state,State_var *first_state,State_var *state_continue ,State_var** state_list,bool state,bool send_all_states,DeclareData *vartmp , bool flag){

State_var *tmpstate = NULL;
State_var *tmp_st = NULL;
DeclareData *tmpst = NULL, *tmpnode = NULL;
Control_block *cntrl=NULL, *loopcontrol = NULL;
DeclareData *tmpvar=NULL;
bool search=false;
bool continueflag=false;
bool node_down = false;
bool loop_created = false , loop_dataflow = false;;
Place_block *tmp_place=NULL;
Transition_block *tmp_tran=NULL;
Path_list *loop_node = NULL , *header_node = NULL ;
Basic_block *block_ret = NULL;
Path_list *exit_node = NULL;
DeclareData *endnode = NULL;
int i=0;

if(state){
	tmpstate = first_state;
	Initialize_StateArray(state_list,10);
	
}
else	tmpstate = state_continue;

while(tmpstate){

	if(flag) tmpvar = tmpstate->state_name;
	else if(!flag) tmpvar = vartmp;
	while(tmpvar){
		//search = false;
		node_down = false;tmp_place = NULL;
		if(!strcmp(tmpvar->name , vartosearch->name)){
			search = true;
			if(send_all_states && !Search_state_in_list(tmpstate,NULL,state_list,10))
				Insert_in_StateArray_list(tmpstate,state_list,10);
				
			else if(!ret_state && !send_all_states) ret_state = tmpstate;
			break;
		}
		//to check if the path following tmpvar is a loop. The loop shouldnt be created here. it returns the exit_nodes as well
		//CHANGED HERE NOW!
		if(!node_down && Check_loop_body(tmpvar,first_state,loop_created,loop_dataflow,exit_node,false,endnode,loopcontrol,false,header_node,true,tmp_place,vartosearch,NULL)){
			//this means vartosearch was found in the loop and the state of the place is checked
			if(tmp_place && Check_state_of_place_input(tmp_place,NULL,tmpstate,NULL,first_state,state_list,10,cntrl)){
				if(send_all_states && state_list)
					Insert_in_StateArray_list(tmpstate,state_list,10);
				else if(!send_all_states)
					ret_state = tmpstate;
				search = true;
				break;
			}
			//send the state which is connected to the varsearch found, only if varsearch is found
			node_down = true;
				while(exit_node){
					if(exit_node->placenode)
						tmpvar = exit_node->placenode->first_trans_node->output_var;
					else if(exit_node->trannode)
				 		tmpvar = exit_node->trannode->output_var;
				 	else if(exit_node->opnode)
				 		tmpvar = exit_node->opnode->output_value;
				 	else if(exit_node->eqnode)
				 		tmpvar = exit_node->eqnode->lhs_value;
				 	else if(exit_node->compnode)
				 		tmpvar = exit_node->compnode->value_out;
				 	
				 	if(tmpvar && Trace_back_node(vartosearch,ret_state,first_state,tmpstate,state_list,false,send_all_states,tmpvar,false)){
				 		search = true;
				 		break;
				 	}
				 	exit_node = exit_node->next_node;	
				}
			//}
			if(search) break;
		}
		if(!node_down && tmpvar->place_ptr){
			tmp_place = tmpvar->place_ptr;
			node_down = true;
			while(tmp_place && Search_var_in_InputList(tmpvar,tmp_place,NULL)){
				//first check all the place inputs(which are not equalto the rhs value of the assignment_graph) and state inputs if they r equal to tmpstate
				tmp_tran = tmp_place->first_trans_node;
				//this function will check all states of the place input n
				while(tmp_tran){
					if(tmp_place->state_place_input){
						//stateflag = true;
						if(Check_state_of_place_input(tmp_place , tmpvar , tmpstate,NULL,first_state,state_list,10,cntrl)){
							//state_check = true;						
							if(!strcmp(tmp_tran->output_var->name , vartosearch->name)){
								//ret_state should not be used when send_all_states is true
								if(send_all_states && state_list)
									ret_state = NULL;
								
								else if(!send_all_states)
									ret_state = tmpstate;
								search = true;
								break;
							}
							// this is for searching vertically tracing one transition output
							else if(Trace_back_node(vartosearch,ret_state,first_state,tmpstate,state_list,false,send_all_states,tmp_tran->output_var,false)){	
								search = true;
								break;
							}
							
							
						}
					}
					else if(!strcmp(tmp_tran->output_var->name,vartosearch->name)){
						tmpnode = tmp_place->first_place_input;
						while(tmpnode){
							if(Trace_back_node(tmpnode,ret_state,first_state,tmpstate,state_list,false,send_all_states,NULL,true)){
								search = true;
								break;
							}
							tmpnode = tmpnode->next_n;
						}
					}
					if(search) break;
					//else continueflag=false;
					tmp_tran = tmp_tran->next_trans_node;
				}	
				if(search) tmp_place=NULL;
				else  tmp_place = tmp_place->next_place;
				//else break; //THIS is going depthwise inside
			} //endof place
			if(search) break;
			else node_down = false;
			//if(!search && continueflag) continue;		//THIS is going depthwise inside
			
		}
		if(!node_down && tmpvar->transition_out){
			node_down = true;
			tmpvar = tmpvar->transition_out->output_var;
			//search = true;
			continue;
		}
		
		if(!node_down && tmpvar->operator_out){
			node_down = true;
			tmpvar = tmpvar->operator_out->output_value;
			//search = true;
			continue;
		}
		if(!node_down && tmpvar->dfgnode_out){
			node_down = true;
			tmpvar = tmpvar->dfgnode_out->output;
			continue;
		}
		if(!node_down && tmpvar->equal_op_out){
			node_down = true;
			tmpvar = tmpvar->equal_op_out->lhs_value;
			//search = true;
			continue;
		}
		//only control nodes mustbe depthwise searched
		//here, even state_name can have this option
		if(!node_down && tmpvar->comparator_out){
			
			//check for the state condition and then pass the output of this comparator
			if(tmpvar->comparator_out->state_condition){
				node_down = true;
				tmp_st = tmpvar->comparator_out->state_condition;
				while(tmp_st){
					if(!strcmp(tmpstate->state_name->name , tmp_st->state_name->name)){
						if(Trace_back_node(vartosearch,ret_state,first_state,tmpstate,state_list,false,send_all_states,tmpvar->comparator_out->value_out,false)){
							if(send_all_states && !Search_state_in_list(tmp_st,NULL,state_list,10))
								Insert_in_StateArray_list(tmp_st,state_list,10);
							else if(!send_all_states)
								 ret_state = tmpstate;
						
							//tmpvar = tmpvar->comparator_out->value_out;
							search = true;
							break;
						}	
					}
					tmp_st = tmp_st->next_state;
				}
			}
			else
				node_down = false;
		}
		if(!node_down && tmpvar->signal_selector_out){
			node_down = true;
			if(tmpvar->signal_selector_out->state_in_signal){
				tmpst = tmpvar->signal_selector_out->state_in_signal;
				while(tmpst){
					if(!strcmp(tmpst->name , tmpstate->state_name->name)){
						if(Trace_back_node(vartosearch,ret_state,first_state,tmpstate,state_list,false,send_all_states,tmpvar->signal_selector_out->out_signal,false)){
						//tmpvar = tmpvar->signal_selector_out->out_signal;
							search=true;
							break;
						}
					}
					tmpst = tmpst->next_n;
				}
			}
			else node_down = false;
		}
		else tmpvar=NULL;
		
	}
	if(!state)	tmpstate=NULL;
	else		tmpstate = tmpstate->next_state;
}
	
	
return search;

}

//search in DFG
//function to search a node in either one basicblock(made until now), or find the node in the previous basicblocks,in thiscase, return the endnode and the block where its found(node_block_ret),
//if search_block is true, then search all previous blocks starting from first_block, if search_block is false, then only search "block"
//here, the fn must also search the loops for nodetocompare, and return the node_ret
bool Search_end_node_BasicBlock(DeclareData *nodetocompare , Basic_block *block , DeclareData*& node_ret , Control_block*& cntrl_ret,bool search_block , Basic_block*& node_block_ret,bool search_node , DeclareData *node_to_trace){

//a basic block will have several inputs either from program_inputs or inputs from some other basic block and every input node goes depth wise

DeclareData *tmp = NULL , *tmpvar = NULL;
Operate_op *tmpop=NULL;
Equal_to_op *tmpeq=NULL;
Path_list *exit_nodes = NULL;
Path_list *tmpnode = NULL;
Compare_operator *tmpcomp=NULL;
Signal_selector *tmpsignal=NULL;
bool node_down = false , continueflag = false;


if(!search_node && block)
	tmp = block->first_block_input;
else tmp = node_to_trace;

//do-while loop is for 
while(block){
	if(continueflag)
		tmp = block->first_block_input;
	
	while(tmp){
		continueflag = false;
		if(Search_node_in_PortList(tmp,block,true)){ //check if tmp is the output of the block
			block = block->next_block;
			continueflag = true;
			break;
		}
		node_down = false;
		if(!strcmp(tmp->name , nodetocompare->name)){
			node_ret = tmp;
			node_down = true;
			if(search_block) node_block_ret = block;
			break;
		}
		//search for the node in dataflow loop - no connectng loop search method implemented here
		
		if(!node_down && Search_node_in_DataLoop(nodetocompare,tmp,node_ret,search_block,block,exit_nodes)){
		//there are two cases: when the nodetocompare node is found ,and when its not found, exit_nodes are rturned. now, search nodetocompare from the path of every exit_nodes
			if(node_ret){
				node_down = true;
				if(search_block) node_block_ret = block;
				break;
			}
			else if(exit_nodes){
				tmpnode = exit_nodes;
				while(tmpnode){
				//search all the path from the exit_nodes recursively
				//the exit_nodes are connected via variable nodes to the loop_path. here, the path should be traced from output of exit node
					if(tmpnode->eqnode)
						tmpvar = tmpnode->eqnode->lhs_value;
					else if(tmpnode->opnode)
						tmpvar = tmpnode->opnode->output_value;
					else if(tmpnode->compnode)
						tmpvar = tmpnode->compnode->value_out;
						
					if(Search_end_node_BasicBlock(nodetocompare,block,node_ret,cntrl_ret,false,node_block_ret,true,tmpvar)){
							node_down = true;
							break;
					}
					else tmpnode = tmpnode->next_node;
				}
				if(!node_down)
					break;
			}
			//in this case, neither node_ret is found nor exit_nodes. so break away from the fn and node_down is false
			else
				break;
			
		}
		if(!node_down && tmp->operator_out){
			//put while loop
			tmpop = tmp->operator_out;
			while(tmpop){
				//tmp = tmp->operator_out->output_value;
				node_down = true;
				//if the nodetocompare is not found by recursively calling function searching from tmp, then continue the while loop else,break 
				if(!Search_end_node_BasicBlock(nodetocompare,block,node_ret,cntrl_ret,search_block,node_block_ret,true,tmp->operator_out->output_value)){
					node_down = false;
					tmpop = tmpop->next_oper;
				}
				else tmpop=NULL;
			}
		}
		if(!node_down && tmp->equal_op_out){
			tmpeq = tmp->equal_op_out;
			while(tmpeq){
				//tmp = tmp->equal_op_out->lhs_value;
				node_down=true;
				if(!Search_end_node_BasicBlock(nodetocompare,block,node_ret,cntrl_ret,search_block,node_block_ret,true,tmp->equal_op_out->lhs_value)){
					node_down = false;
					tmpeq = tmpeq->next_equal;
				}
				else tmpeq=NULL;
			}
		}
		if(!node_down && tmp->comparator_out){
			// it will go into a control block
			tmpcomp = tmp->comparator_out;
			while(tmpcomp){
				//tmp = tmp->comparator_out->value_out;
				if(Search_control_nodes(tmp->comparator_out->value_out , cntrl_ret,node_ret,nodetocompare,NULL)){
					node_down=true;
					break;
				}
				else{
					node_down=false;
					tmpcomp = tmpcomp->next_comparator;
				}
			}
		}
		if(!node_down && tmp->signal_selector_out){
			tmpsignal = tmp->signal_selector_out;
			while(tmpsignal){
				//tmp = tmp->signal_selector_out->out_signal;
				if(Search_control_nodes(tmp->signal_selector_out->out_signal,cntrl_ret,node_ret,nodetocompare,NULL)){
					node_down = true;
					break;
				}
				else{
					node_down = false;
					tmpsignal = tmpsignal->next_selector;
				}
			}
		}
		if(!node_down) tmp = tmp->next_n; //to the next input of the block
		else tmp = NULL;
	}
	if(continueflag) continue;
	if(node_down) break;
	else if(search_block && continueflag) block = block->next_block;
	else block=NULL;
		
} //end of while

return node_down;

}

//DFG search
//function to first check if the path from startfromvar is in a DFG dataloop. If yes, then search for nodetocompare(petri),if yes, then return the value through node_found. 
// if there is a loop and nodetocompare isnt found, then obtain the exit points of this DFG loop, and return back the exit points to search path of each exit_point depthwise.
//search in DFG

bool Search_node_in_DataLoop(DeclareData *nodetocompare,DeclareData *startfromvar,DeclareData*& node_found,bool search_block,Basic_block *data_block,Path_list*& exit_point){

bool search = false , flag=false;
int num=0 ,i=0;
DeclareData *arr_tmp[10];
bool dataflow_check = false , loop_created = false;
Place_block *tmp_place = NULL;
Control_block *loopcontrol = NULL;
Path_list *header = NULL;
DeclareData *noderet = NULL;
Path_list *loopempty = NULL;
DeclareData *varempty = NULL;
Path_list *temp_loop[10];

//this fn will search for loops in all the basic blocks, just following startfromvar
//here the DFG should be searched for the loop,and startfromvar is a node in dfg. so search_dfg is true.
//searchflag is also made true, so that it searches for nodetocompare in the loop. if yes, then noderet will have value. if not check if exit_point has some value
if(Check_loop_body(startfromvar,first_state,loop_created,dataflow_check,exit_point,true,noderet,loopcontrol,false,header,true,tmp_place,nodetocompare,NULL)){
	//here the search_dfg flag is made true, and noderet is the node returned if nodetocompare is found.
	if(noderet)
		search = true;
	else if(exit_point)
		search = true;
	else
		search = true;
	
}

/*
if(Search_back_petri_model(startfromvar,NULL,true,true,first_state,num,false,loopempty,false,arr_tmp,10,search_block,data_block,false,varempty)){
	//create a loopnode_list
	
	flag = Search_back_petri_model(startfromvar,NULL,true,false,first_state,num,false,loopempty,false,arr_tmp,10,search_block,data_block,false,varempty);
	//find nodetocompare in the loop
	//block_ret is the basic_block if the loop isfrom a different basic block 
	//here must assume that arr_tmp has the list of pointers to those variables which are in loop.
	//thus, there is no need to go through the loop to search nodetocompare.just search the list for nodetocompare and return the value if found.
	if(Search_loop_for_node(arr_tmp,10,nodetocompare,noderet)){
		node_found = noderet;
		search = true;
	}
		// memory of exit_point is alrdy allocated in the Insert_pathlist function,no need to do here
	else if(Search_exitpoint_DataLoop(startfromvar,arr_tmp,10,exit_point)){
		search = true;
		
	}
	
}
*/

return search;

}

//function to search the exit point of a dataflow loop in DFG graph
//exit_point obtains the set of exit nodes in the loop
bool Search_exitpoint_DataLoop(DeclareData *startvar, DeclareData** arr_tmp,int size,Path_list*& exit_point){

DeclareData *tmp = NULL;
bool search = false;
int i;

//this fn will search the elements of arr_tmp and starting from startvar, if the successive node output generated from startvar,doesnt match the element of arr_tmp, then it is an exit point. if it matches, then continue with the loop. for continuing the loop, startvar is changed to the output of that node.


while(i<=size && startvar){
	
	if(startvar->operator_out){
		tmp = startvar->operator_out->output_value;
		//if it doesnt match with the next var in the loop
		if(strcmp(arr_tmp[i]->name,tmp->name)){
			search = true;
			Insert_in_pathlist_list(exit_point,NULL,NULL,NULL,startvar->operator_out,NULL,NULL,NULL);
		}
		 startvar = tmp;
	}
	if(!search && startvar->equal_op_out){
		tmp = startvar->equal_op_out->lhs_value;
		if(strcmp(arr_tmp[i]->name,tmp->name)){
			search = true;
			Insert_in_pathlist_list(exit_point,NULL,NULL,startvar->equal_op_out,NULL,NULL,NULL,NULL);
		}
		 startvar = tmp;
	}
	else startvar = NULL;
	i++;
	


}


return search;

}



//change this function
//function to search a variable node from the list of pointers holding the variable nodes of a loop

bool Search_loop_for_node(int size,DeclareData *nodetocompare,DeclareData*& node_ret){

int i = 0;
bool search = false;

while(i<size){
	if(loop_list[i] && loop_list[i]->eqnode && !strcmp(nodetocompare->name,loop_list[i]->eqnode->lhs_value->name)){
		node_ret = loop_list[i]->eqnode->lhs_value;
		search = true;
	}
	else if(loop_list[i] && loop_list[i]->opnode && !strcmp(nodetocompare->name,loop_list[i]->opnode->output_value->name)){
		node_ret = loop_list[i]->opnode->output_value;
		search = true;
	}
	
i++;

}

return search;

}






//this function searches the compsearch OR sigsearch as a control block in the graph of control nodes and returns in cntrl

bool Search_from_control_block(Compare_operator *compsearch,Signal_selector *sigsearch,Control_block*& cntrl){

Control_block *tmpcontrol=NULL;
Control_block *control_tmp=NULL;
bool search=false;

tmpcontrol = first_control_node;
while(tmpcontrol){
	control_tmp = tmpcontrol;
	while(control_tmp){
		if(compsearch && control_tmp->control_compare_node == compsearch){
			search=true;
			cntrl = control_tmp;
			break;
		}
		else if(sigsearch && control_tmp->signal_select_node == sigsearch){
			search=true;
			cntrl = control_tmp;
			break;
		}
		if(!search && control_tmp->result_control)
			control_tmp = control_tmp->result_control;
		else control_tmp=NULL;
	}
	tmpcontrol = tmpcontrol->next_control_block;
	
}

return search;

}



//DFG search only
//only state control blocks are inserted in the direct control block list
//FINAL VERSION OF THIS FUNCTION

//this function is to search nodetocompare in the control tree, which could be started from tmpvar and traced depth and breadthwise
//this function should also search nodetocompare in the entire control tree, and return node_ret and cntrl_ret where the node_ret is found
//search_block is the control block if the function has to search in this specific block else search from tmpvar(which mustb e first found in which controlblock)
bool Search_control_nodes(DeclareData *tmpvar , Control_block*& cntrl_ret , DeclareData*& node_ret, DeclareData *nodetocompare,Control_block *search_block){

Control_block *tmpcontrol = NULL;
Control_block *tmp=NULL;
bool node_down=false;
bool node_found=false;

Control_block *control_found=NULL;

tmpcontrol = first_control_node;


//tmpvar is searched in the control block graph
if(tmpvar){
	if(!strcmp(nodetocompare->name , tmpvar->name)){
		node_ret = tmpvar;
		node_found = true;
		node_down = true;
		//break;
	}
	
	if(!node_down && tmpvar->comparator_out){
		if(Search_control_nodes(tmpvar->comparator_out->value_out,cntrl_ret,node_ret,nodetocompare,search_block) && Search_from_control_block(tmpvar->comparator_out,NULL,control_found)){
			cntrl_ret = control_found;
			node_found=true;
			node_down = true;
		}
		//else tmpvar = control_found->control_out;
	}
	if(!node_down && tmpvar->signal_selector_out){
		if( Search_control_nodes(tmpvar->signal_selector_out->out_signal,cntrl_ret,node_ret,nodetocompare,search_block ) && Search_from_control_block(NULL,tmpvar->signal_selector_out,control_found)){
			cntrl_ret = control_found;
			node_found=true;
			node_down = true;
		}
	//	else tmpvar = control_found->control_out;
	}
	/*
	if(!node_down && tmpvar->operator_out && tmpvar->operator_out->op_type == '<' || '>'){
		if(Search_control_nodes(tmpvar->operator_out->output_value,cntrl_ret,node_ret,nodetocompare,search_block)){
			node_found = true;
			node_down = true;
		}
	}
	*/
	//else node_found=false;
	
}


	
//}
//this option is for checking all control nodes
 else if(!tmpvar){
	//check all control nodes, option 1: if tmpcontrol has state_node, or control_compare_node or signal_select_node or control_dfg_node
	if(!search_block) tmpcontrol = first_control_node;
	else tmpcontrol = search_block;
	while(tmpcontrol){
		//do{
			node_down = false;
			if(tmpcontrol->state_node){
				node_down = true;
				tmp = tmpcontrol->result_control;
				while(tmp){
					if(Search_control_nodes(NULL,cntrl_ret,node_ret,nodetocompare,tmp)){
						node_found=true;
						if(!cntrl_ret) cntrl_ret = tmp;
						node_down = true;
						break;
					}
					
					tmp = tmp->next_control_block;
				}
				if(!node_found && tmpcontrol->control_out && Search_control_nodes(tmpcontrol->control_out,cntrl_ret,node_ret,nodetocompare,NULL)){
					if(!cntrl_ret) cntrl_ret = tmpcontrol;
					node_found = true;
					break;
				}
				if(!node_found)
					 node_down = false;
				
			}
			if(!node_down && tmpcontrol->control_dfg_node){
				//this function already checks for the exit nodes of the control_loop,so no need to check them here explicitly
				node_down = true;
				if(Search_node_in_Control_Loop(nodetocompare,tmpcontrol->control_dfg_node,node_ret)){
					cntrl_ret = tmpcontrol;
					node_found = true;
					break;
				}
				else if(tmpcontrol->control_out && Search_control_nodes(tmpcontrol->control_out,cntrl_ret,node_ret,nodetocompare,NULL)){
						if(!cntrl_ret) cntrl_ret = tmpcontrol;
						node_found = true;
						break;
					//node_down = true;
					//tmpvar = tmpcontrol->control_out;
				}
				else if(tmpcontrol->result_control && Search_control_nodes(NULL,cntrl_ret,node_ret,nodetocompare,tmpcontrol->result_control)){
					node_found = true;
					if(!cntrl_ret) cntrl_ret = tmpcontrol;
					break;
				}
				else node_down = false;
				
			}
			if(!node_down && tmpcontrol->control_compare_node){
			//here you must send the inputs to this control_compare to check and then the outputs
				node_down = true;
				tmpvar = tmpcontrol->control_compare_node->condition_value;
				if(tmpvar && Search_control_nodes(tmpvar,cntrl_ret,node_ret,nodetocompare,NULL)){
					if(!cntrl_ret) cntrl_ret = tmpcontrol;
					node_found = true;
					break;
				}
				tmpvar = tmpcontrol->control_compare_node->lhs_compare;
				if(tmpvar && Search_control_nodes(tmpvar,cntrl_ret,node_ret,nodetocompare,NULL)){
					if(!cntrl_ret) cntrl_ret = tmpcontrol;
					node_found = true;
					break;
				}
				tmpvar= tmpcontrol->control_compare_node->value_out;
				if(Search_control_nodes(tmpvar , cntrl_ret,node_ret,nodetocompare,NULL)){
					if(!cntrl_ret) cntrl_ret = tmpcontrol;
					node_found = true;
					break;
				}
				else if(tmpcontrol->result_control){
					tmp = tmpcontrol->result_control;
					while(tmp){
						if(Search_control_nodes(NULL,cntrl_ret,node_ret,nodetocompare,tmp)){
							node_found=true;
							if(!cntrl_ret) cntrl_ret = tmp;
							node_down = true;
							break;
						}
						tmp = tmp->next_control_block;
					}
				}
				else node_down = false;
				if(node_found) break;
				
				
			}
			if(!node_down && tmpcontrol->signal_select_node){
				tmpvar = tmpcontrol->signal_select_node->in_signal_list;
				while(tmpvar){
					if(Search_control_nodes(tmpvar,cntrl_ret,node_ret,nodetocompare,NULL)){
						node_found = true;
						break;
					}
					tmpvar = tmpvar->next_n;
				}
				if(node_found) break;
				tmpvar = tmpcontrol->signal_select_node->out_signal;
				if(Search_control_nodes(tmpvar,cntrl_ret,node_ret,nodetocompare,NULL)){
					node_found=true;
					break;
				}
				else if(tmpcontrol->result_control){
					tmp = tmpcontrol->result_control;
					while(tmp){
						if(Search_control_nodes(NULL,cntrl_ret,node_ret,nodetocompare,tmpcontrol->result_control)){
							node_found = true;
							if(!cntrl_ret) cntrl_ret = tmpcontrol;
							node_down = true;
							break;
						}
						tmp = tmp->next_control_block;
					}
					if(node_found) break;
				}
				else
					node_down = false;
				//tmpvar = tmpcontrol->control_out;
			}
		if(!node_found) tmpcontrol = tmpcontrol->next_control_block;
		//if(!tmpcontrol) tmpcontrol = tmpcontrol->result_control;
		//else tmpcontrol = NULL;
		if(node_found)
			break;
	}
}

return node_found;

}



//function to search a var node similar to varsearch in the search_loop(if search_loop exists, then forsure the control loop exists), and send back the returned value through var_found
bool Search_node_in_Control_Loop(DeclareData *varsearch, DFG_block *search_loop, DeclareData*& var_found){

bool search = false;
bool loopfound = false;
bool start = false;
bool changeflag = false;
Path_list *node = NULL;
Equal_to_op *tmpeq = NULL;
DeclareData *arr_data[10];
DeclareData *tmp_node = NULL;
DeclareData *tmpvar=NULL;
DeclareData *varempty = NULL;
int num;
Basic_block *block_empty = NULL;
Path_list *loopempty = NULL;
Path_list *nodeconnect = NULL;

if(search_loop->operation_graph){
	//either of the inputs is an integer, thus the other input has to be a part of the loop
	tmpvar = search_loop->operation_graph->output_value;
	
}
else if(search_loop->assignment_graph)
	tmpvar = search_loop->assignment_graph->lhs_value;
	
	
tmp_node = tmpvar;	
	
	while(tmpvar){
		//check for the varsearch here
		loopfound = false;changeflag = false;
		if(start && !strcmp(tmpvar->name,varsearch->name)){
			var_found = tmpvar;
			search = true;
			break;
		}
		
		start = true;
		 if(tmpvar->operator_out){
			start = true;
			if(Search_back_loop(tmpvar->operator_out->output_value,search_loop,varsearch,var_found)){
				if(var_found){
					tmpvar = NULL;
					search = true;
					break;
				}
				else
					//tmpvar = tmpvar->operator_out->output_value;
					loopfound = false;
				
			}
	
				//then its an exit node, check if the exit node is leading upto a COMP or SS,only then proceed depthwise
			else if(Search_ControlNodes_depthwise(tmpvar->operator_out->output_value,node,false,true,NULL,true,nodeconnect,false)){
				tmpvar = tmpvar->operator_out->output_value;
				loopfound = true;
				changeflag = true;
			}
			if(!loopfound){
				tmpvar = tmpvar->operator_out->output_value;
				changeflag = true;
			}
				
		}
		 if(!loopfound && tmpvar->equal_op_out){
		 	tmpeq = tmpvar->equal_op_out;
		 	while(tmpeq){
		 		tmpvar = tmpeq->lhs_value;
			 	if(Search_back_loop(tmpeq->lhs_value,search_loop,varsearch,var_found)){
			 		if(var_found){
			 			tmpvar = NULL;
			 			search = true;
			 			break;
			 		}
			 		else
			 			
			 			changeflag = true;
			 			//tmpvar = tmpeq->lhs_value;
			 			//tmpeq = tmpeq->next_equal;
			 			
			 	}
				else if(Search_ControlNodes_depthwise(tmpeq->lhs_value,node,false,true,NULL,true,nodeconnect,false)){
					tmpvar = tmpeq->lhs_value;
					changeflag = true;
					break;
				}
				//if(!loopfound)
				//	tmpvar = tmpeq->lhs_value;
					
				tmpeq = tmpeq->next_equal;		
			}
			if(search) break;
		}
		if(!changeflag)
			tmpvar = NULL;
		
	}
	
	
return search;
	
}


//fn to trace varsearch in dfgloop . its known here that its a dfg controlloop. 
bool Search_back_loop(DeclareData *var_loop,DFG_block *dfgloop,DeclareData *varsearch,DeclareData*& varfound){

DeclareData *tmp = NULL;
bool start = false;

bool search = false;

if(var_loop)
	tmp = var_loop;
else if(dfgloop->assignment_graph){
	tmp = dfgloop->assignment_graph->lhs_value;
	var_loop = tmp;
}
else if(dfgloop->operation_graph){
	tmp = dfgloop->operation_graph->output_value;
	var_loop = tmp;
}

while(tmp){
	if(start && !strcmp(tmp->name,var_loop->name)){
		search = true;
		break;
	}
	start = true;
	if(tmp->operator_out){
		if(!strcmp(varsearch->name,tmp->operator_out->output_value->name)){
			search = true;
			varfound = tmp->operator_out->output_value;
			break;
		}
		else
			tmp = tmp->operator_out->output_value;
		continue;
	}
	else if(tmp->equal_op_out){
		if(!strcmp(varsearch->name,tmp->equal_op_out->lhs_value->name)){
			search = true;
			varfound = tmp->equal_op_out->lhs_value;
			break;
		}
		else
			tmp = tmp->equal_op_out->lhs_value;
		continue;
	}
	else tmp = NULL;
}


return search;

}




//fn to search a particular "search" state or searchvar in list of state pointers
bool Search_state_in_list(State_var *search , DeclareData *searchvar,State_var** list,int size){

//State_var *tmp = NULL;
int i =0;
bool flag = false;

while(i<size && list[i]){
	if((search && !strcmp(search->state_name->name,list[i]->state_name->name)) || (searchvar && !strcmp(searchvar->name,list[i]->state_name->name))){
		flag = true;
		break;
	}
	i++;
}


return flag;

}






//this function first checks if placenode has state input or not. if yes, check to match with statenode, if not then check the place inputs, 
//if nodetocheck matches with the rhs value of the tran then, 
//if no nodecheck, then all the control inputs are checked and any input from a state already created as control block ,search is true
//function is called to check if the state of the control inputs are already created as control blocks
bool Check_state_of_place_input( Place_block *placenode , DeclareData *nodetocheck , State_var *statenode , Transition_block *tran,State_var *first_state,State_var** statelist_ret,int list_size,Control_block*& control_ret){

DeclareData *tmpnode=NULL;
bool search=false;
State_var *state_ret=NULL;
State_var *tmp_state = NULL;
int i=0;
//State_var *statelist[10];

//first: check the nodetocheck is a state name or not
//second: if yes, then send search is true, since it has to be the same as statenode
//if no, check for the state input if it exists and check if the state input is the same as statenode
// if no, then check for node if its same as rhs value of assignment graph
//if yes, then search is false
//if no, then search is true since its implied its from the same state as statenode

if(nodetocheck && Search_var_from_statelist(nodetocheck, tmp_state,false))
	search = true;
	
else if(statenode && placenode && placenode->state_place_input){

	tmpnode = placenode->state_place_input;
	//tmp_state = new State_var;
	//Initialize_nodes(NULL,NULL,tmps,NULL,NULL,NULL);
	while(tmpnode){
		if(Search_var_from_statelist(tmpnode,tmp_state,false)){
			Insert_in_StateArray_list(tmp_state,statelist_ret,list_size);
		}
		
 		if(!strcmp(tmpnode->name , statenode->state_name->name))
			search = true;

		tmpnode=tmpnode->next_n;
	}
}
//this case will only occur if there is no statenode to match to,and the function is called to check if the state of the control inputs are already created as control blocks
/*
if(!search && placenode){
	//check for the control inputs to the place. If the state in which it is generated=state_ret. check if state_ret has one state equal to statenode
	if(!nodetocheck) tmpnode = placenode->first_place_input;
	else tmpnode = nodetocheck;
	while(tmpnode){
			//state_ret in this case,should contain all the states which generate tmpnode
		//if(Trace_back_node(tmpnode,stateret,	
		//if(Check_state_of_place_input(NULL,tmpnode,statenode,tran,first_state,statelist_ret,list_size,control_ret)){
		if(Trace_back_node(tmpnode,state_ret,first_state,NULL,statelist_ret,true,true)){
			if(!nodetocheck && !strcmp(tmpnode->name,placenode->first_trans_node->data_node->assignment_graph->rhs_value->name))
				continue;
				//send_all_states flag is true, so all the states are sent via statelist
			
			while(i<list_size && statelist_ret[i]){
				if(!statenode && Search_state_from_controlnode_list(statelist_ret[i],first_control_node,control_ret)){
					search=true;
					break;
				}
				i++;
				//tmp=tmp->next_state;
			}
			if(search) break;
		}
		tmpnode = tmpnode->next_n;
	}
}
*/
if(!search && tran && strcmp(nodetocheck->name , tran->data_node->assignment_graph->rhs_value->name))
	search = true;
	


return search;

}




//this function traces in a depth-search manner from start_node to the node which is connected to a particular state(ret_state)
//if a node is connected to more than one state, then the earlier state is found out and returned
bool Trace_depthwise_node( DeclareData *start_node, State_var *first_state,State_var*& ret_state){

DeclareData *tmpstate=NULL;
State_var *tmps=NULL;
DeclareData *tmp=NULL;
Control_block *tmp_cn = NULL;
Compare_operator *tmpcomp=NULL;
bool search;
bool success=false;

	
	tmp = start_node;
	tmps= new State_var;
	Initialize_nodes(NULL,NULL,tmps,NULL,NULL,NULL);
	while(tmp){
		search=true;
		if(tmp->place_ptr){
			tmpstate = tmp->place_ptr->state_place_input;
			while(tmpstate){
				if(tmpstate->prev_n){
					if(Search_var_from_statelist(tmpstate,ret_state,false)){
						tmps->next_state = new State_var;
						Initialize_nodes(NULL,NULL,tmps->next_state,NULL,NULL,NULL);
						tmps->next_state->state_name = ret_state->state_name;
						Insert_in_state_list(tmps->next_state,tmps);
						success=true;
						if(Find_earlier_state(tmps,first_state,first_control_node))
							search = false;
						else
							search = true;
					}
				}
				else{
					if(Search_var_from_statelist(tmpstate , ret_state,false))
						tmps->state_name = ret_state->state_name;
				}
				tmpstate=tmpstate->next_n;
				
			}
			//while condition for searching for place_input of the tmp->place_ptr
			
			if(!success){
				tmpstate = tmp->place_ptr->first_place_input;
				Trace_back_node(tmpstate , ret_state,first_state,NULL,NULL,true,false,NULL,true);
			}
			else 
				ret_state = tmps;
			//else ret_state=NULL;
			break;
							
		}
		 else if( tmp->operator_out){
			tmp = tmp->operator_out->output_value;
		}
		else if(tmp->dfgnode_out){
			tmp = tmp->dfgnode_out->output;
		}
		else if(tmp->signal_selector_out){
			tmpstate = tmp->signal_selector_out->state_in_signal;
			while(tmpstate){
				if(tmpstate->prev_n){
					if(Search_var_from_statelist(tmpstate,ret_state,false)){
						tmps->next_state = ret_state;
						Find_earlier_state(tmps,first_state,first_control_node);
						
					}
				}
				else{
					if(Search_var_from_statelist(tmpstate,ret_state,false))
						tmps->state_name = ret_state->state_name;
					
				}
				tmpstate = tmpstate->next_n;
			}
			ret_state= tmps;
			search=true;
			break;
		}
		else if(tmp->comparator_out){
			tmpcomp = tmp->comparator_out;
			while(tmpcomp){
				if(tmpcomp->state_condition){
					ret_state = tmpcomp->state_condition;
					search=true;
					break;
				}
			//if there is no state condition, then trace the input of this comparator and check which state it is generated, and it returns ret_state
				else if(Trace_back_node(tmpcomp->lhs_compare,ret_state,first_state,NULL,NULL,true,false,NULL,true)){
					search=true;
					break;
				}

				else if(Trace_back_node(tmpcomp->value_out,ret_state,first_state,NULL,NULL,true,false,NULL,true)){
					search=true;
					break;
				}
				tmpcomp = tmpcomp->next_comparator;
			}			
		}
		else if(tmp->equal_op_out){
			
			tmp = tmp->equal_op_out->lhs_value;
		}
		
		
		else tmp=NULL;
	
	}
	if(ret_state){
		//check if the state is already created as a control block
		tmp_cn = first_control_node;
		while(tmp_cn){
			if(tmp_cn->state_node && !strcmp(tmp_cn->state_node->state_name->name , ret_state->state_name->name)){
				search = true;
				break;
			}
			else	search = false;
			tmp_cn = tmp_cn->next_control_block;
		}
	}
	

	

return search;


}

//function to find the earlier state of the two states passed to this function
//if sort is true it means that the state has not been created as  a control block
//if sort is false, it mean that the state has been created as a control block already returned as sort_state
bool Find_earlier_state(State_var*& sort_state,State_var *first_state, Control_block *first_control_node){

State_var *tmp=NULL;
State_var *tmp1=NULL;
Control_block *tmpcntrl = NULL;
bool sort=false;
bool flag=false;

tmp = first_state;

//sort_state contains two states as a list

while(tmp){
	tmp1 = sort_state;
	while(tmp1){
		if(!strcmp(tmp1->state_name->name , tmp->state_name->name)){
			//if(!Search_state_from_controlnode_list(tmp1,first_control_node))
			sort_state = tmp1;
			sort_state->next_state=NULL;
			sort_state->prev_state=NULL;
			flag=true;
			if(!Search_state_from_controlnode_list(tmp1,first_control_node,tmpcntrl))
				sort=true;
			else	sort = false;
			break;
		}
		
		else tmp1 = tmp1->next_state;
	}
	if(flag) tmp=NULL;
	
}

return sort;
//if(!sort) delete_data_list(NULL,sort_state);


}


//this function searches if the state "searchnode" is already existing in the control block list
bool Search_state_from_controlnode_list(State_var *searchnode,Control_block *first_control_node, Control_block*& control_ret){

Control_block *tmp=NULL;
bool flag=false;

tmp = first_control_node;
while(tmp){
	if(tmp->state_node && !strcmp(tmp->state_node->state_name->name,searchnode->state_name->name)){
		flag = true;
		control_ret = tmp;
		break;
	}
	else flag=false;
	tmp = tmp->next_control_block;
}

return flag;


}


//fn to insert the state pointer in the state array list
void Insert_in_StateArray_list(State_var *state, State_var** State_list,int size){

int i=0;


while(State_list[i] && i<size)
	
	i++;

State_list[i] = state;


}





//function to insert a new control block in the list of control nodes of the graph, this is just a basic list to keep all the nodes in check
void Insert_in_control_list(Control_block*& first_node , Control_block *control_node){

Control_block *tmp=NULL;
if(!first_node){
	first_node = control_node;
	first_node->next_control_block=NULL;
}
else{
	for(tmp = first_node ; tmp->next_control_block!=NULL; tmp=tmp->next_control_block);
	tmp->next_control_block = control_node;
	control_node->next_control_block=NULL;
	control_node->prev_control_block = tmp;
}


}


//thisfunction is to insert a child node in the list of controlnode->control_in or controlnode->result_control
void Insert_in_child_list( Control_block *parentlist , Control_block *childnode){

Control_block *tmp=NULL;
//DeclareData *tmp=NULL;

//if(result_control){
	//this is only for the non-state nodes getting connected from the state nodes
	for(tmp = parentlist ; tmp->next_control_block!=NULL; tmp=tmp->next_control_block);
	tmp->next_control_block = childnode;
	childnode->next_control_block=NULL;
	childnode->prev_control_block = tmp;
//}



}

//fn to insert a new node in the list starting from node_first
void Insert_in_pathlist_list(Path_list*& node_first,Place_block *plnode,Transition_block *trnode,Equal_to_op *equalnode,Operate_op *oper,Compare_operator *comp,DFG_block *dfg,Signal_selector *sig){
	
Path_list *tmpnode = NULL;
Path_list *tmp = NULL;

tmpnode = new Path_list;
Initialize_array_pointer(tmpnode);	

if(plnode) tmpnode->placenode = plnode;
else if(trnode) tmpnode->trannode = trnode;
else if(equalnode) tmpnode->eqnode = equalnode;
else if(oper) tmpnode->opnode = oper;
else if(comp) tmpnode->compnode = comp;
else if(dfg) tmpnode->dfgnode = dfg;
else if(sig) tmpnode->signalnode = sig;

if(!node_first)
	node_first = tmpnode;
else{
	for(tmp = node_first ; tmp->next_node!=NULL; tmp = tmp->next_node);
	tmp->next_node = tmpnode;
	tmpnode->next_node = NULL;
}
	
}

//fn to insert a node or a list to the existing list of exit_ret or copy the list to exit_ret if its NULL
void Insert_node_in_pathlist(Path_list*& exit_ret,Path_list *tmpnode){

Path_list *tmp = NULL;

if(!exit_ret) exit_ret = tmpnode;
else{
	for(tmp = exit_ret ; tmp->next_node!=NULL ; tmp = tmp->next_node);
	tmp->next_node = tmpnode;
	
}

}


//fn to insert the control block pointer "block" to the array of contrrol_pointers
void Insert_in_BasicBlock_array(Basic_block *block_loop,int size,Control_block *block){

int i=0;
for(i=0; i<size; i++){
	if(block_loop->control_node_pointers[i])
		continue;
	else break;
}
block_loop->control_node_pointers[i++] = block;


}




//function to insert the data node in the inputnode list of a datablock
void Insert_in_node_list(DeclareData *node_first , DeclareData *nodetoinsert){

DeclareData *tmp=NULL;

if(!node_first)
	node_first = nodetoinsert;
	
else{
	for(tmp = node_first ; tmp->next_n!=NULL; tmp=tmp->next_n);
	tmp->next_n = nodetoinsert;
	nodetoinsert->next_n=NULL;
}



}

//function to assign values of a control block's state_node
void assign_controls(State_var *nodeto, State_var *nodefrom , Equal_to_op *node_to, Equal_to_op *node_from,bool select){

if(select){
	assign_value(nodeto->state_name,nodefrom->state_name);
	//nodeto->state_name = nodefrom->state_name;
	nodeto->next_state=NULL;
	nodeto->prev_state=NULL;
	nodeto->signal_selector_out=NULL;
}
else{
	node_to->lhs_value = node_from->lhs_value;
	node_to->opsymbol = node_from->opsymbol;
}

}

//fn to insert a basic_block in the list of controlblock->bb_ptr
void Insert_in_BasicBlock_list(Control_block *ctrlnode , Basic_block *bbnode){

Basic_block *tmp=NULL;
Basic_block *start = NULL;

if(ctrlnode) start = ctrlnode->bb_ptr;
else{
	 if(!first_basic_block)
	 	first_basic_block = bbnode;
	 else
		 start = first_basic_block;
}

if(start){
	for(tmp = start ; tmp->next_block!=NULL; tmp = tmp->next_block);
	tmp->next_block = bbnode;
	bbnode->next_block = NULL;
	bbnode->prev_block=tmp;
}

}


//fn to initialize the node pointer
void Initialize_array_pointer(Path_list *node1){

node1->varnode=NULL;
node1->placenode=NULL;
node1->trannode=NULL;
node1->opnode=NULL;
node1->eqnode=NULL;
node1->compnode=NULL;
node1->signalnode=NULL;
node1->dfgnode=NULL;
node1->next_node=NULL;

}

void Initialize_array(DeclareData **arr_ptr,int size){

int i;

for(i=0;i<size;i++)
	arr_ptr[i] = NULL;
	
}


void Initialize_StateArray(State_var **state_ptr , int size){

int i;
for(i=0; i<size ; i++)
	state_ptr[i] = NULL;
}


//fn to delete the nodes of Path_list type or any other type
void delete_node_list(Path_list*& dominator_ret){

Path_list *tmp = NULL;

tmp = dominator_ret;
while(dominator_ret){

	tmp = dominator_ret->next_node;
	delete dominator_ret;
	dominator_ret=NULL;
	dominator_ret = tmp;
	
}

}





