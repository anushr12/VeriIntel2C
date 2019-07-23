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
#include "petri_graphTransform.h"
//#include "analysis_parse.cpp"



using namespace std;

#ifdef VERIFIC_NAMESPACE
using namespace Verific ;
#endif

Control_block *first_control_node;
Basic_block *first_basic_block;
Mux_node *first_mux;
DeclareData *program_inputs; //these are the actual input variables to the verilog code


int Transform_to_flow_graph(State_var *first_state, Place_block *first_place_node,Place_block *first_parallel_place, Equal_to_op *first_EqualTo_node){


	if(first_EqualTo_node || first_parallel_place)
		// there are unrolled paths in this graph (full or partial)
		Create_dataflow_unrolled(first_parallel_place,first_EqualTo_node,first_state);
	else
		Create_dataflow(first_state,first_place_node);

}


void Create_dataflow_unrolled(Place_block *first_parallel_place, Equal_to_op *first_EqualTo_node, State_var *first_state){

Equal_to_op *first_n=NULL;
bool state_exists = false;
State_var *statenode=NULL;
Place_block *tmp_p=NULL;

//if state_exists is false, then the state found does not exist currently as a control block, thus create a control block n then put the path in its associated basic blk
// if state_exists is true, then the state exists already as a control block, thus search the control block list for the statenode name and insert the path in its associated blk
//with this combination, if statenode exists, then there exists some state, but if no statenode, then there is no state for that path and then call Create_fully_unrolled_Graph

	if(first_EqualTo_node){
	
		// these nodes do not go inside any control block. Now,search depthwise for each parallelequalto node if its associated with any state
		first_n = first_EqualTo_node;
		while(first_n){
			state_exists = Trace_depthwise_node(first_n->lhs_value, first_state,statenode);
			if(state_exists)
				Create_control_and_basic_blocks(statenode, first_n->rhs_value,false,true,first_state);
				
			else if(!state_exists && statenode)
				Create_control_and_basic_blocks(statenode,first_n->rhs_value,true,true,first_state);
			else{
				// this case shows that there are no any states in the path of this equalto node, which implies all the equalto nodes do not have a state, so the entire graph is built inside a single basic block
				Create_fully_unrolled_graph(first_EqualTo_node);
				break;
			}
			first_n = first_n->next_equal;
		}
	
	}
	else if(first_parallel_place){
		tmp_p = first_parallel_place;
		while(tmp_p){
			trans_p = tmp_p->first_trans_node;
			while(trans_p){
				if(Trace_depthwise_node(trans_p->output_var,first_state,statenode))
					Create_control_and_basic_blocks(statenode , trans_p->data_node->rhs_value,first_state);
				//no else condition
				trans_p = trans_p->next_trans_node;
			}
			tmp_p = tmp_p->next_place;
		}
		
	}



}

//function to create the control block nodes of (state) and insert the path starting from pathnode,
//equalnodes_exist is to indicate if this function is called when equalnodes exist, n if its false, then its called when equalnodes do not exist
void Create_control_and_basic_blocks(State_var *state , DeclareData *pathnode,bool control_create,bool equalnodes_exist,State_var *first_state){



if(control_create && equalnodes_exist){
	//create a control block associated with the statenode
	// since, the control block will b created, the starting node pathnode, shall be the inputs to the associated basic block
	Control_block *control = new Control_block;
	Initialize_nodes(NULL,NULL,NULL,control,NULL,NULL);
	//make this control node acc. to the state, 
	if(state){
		control->state_node = new State_var;
		Initialize_nodes(control->state_node,NULL,NULL,NULL,NULL,NULL,NULL);
		assign_controls(control->state_node,state);
		control->bb_ptr = new Basic_block;
		Initialize_nodes(NULL,NULL,NULL,NULL,control->bb_ptr,NULL);
		Insert_path_in_BasicBlock(control,control->bb_ptr,pathnode,first_state);
		Insert_in_control_list(first_control_node , control);
	}
	
	

}





}

//function to insert the path from startnode TO the node until the state is control_st->state_node
void Insert_path_in_BasicBlock(Control_block *control_st,Basic_block *datablock, DeclareData *startnode,State_var *first_state){

DeclareData *temp=NULL;
DeclareData *tmpdata=NULL;
State_var *tmpst = NULL;
Control_block *prev_control = NULL;
Control_block *tmp_control = NULL;
DeclareData *endnode=NULL;
DeclareData *controlnode=NULL;
bool node_down=false;
bool stateflag=false;

tmpst = control_st->state_node;

temp = startnode;

do{

//this is only for first case and for initializign the block;s inputs
	if(temp == startnode){
		if(temp->data_type == input){
			tmpdata = new DeclareData;
			assign_value(tmpdata,temp);
			Insert_in_node_list(program_inputs,tmpdata);
			datablock->first_block_input = program_inputs;
		}
		else{
			tmpdata = new DeclareData;
			assign_value(tmpdata,temp);
			Insert_in_node_list(datablock->first_block_input,tmpdata);
		
		}
		
	}
	//first iteratively insert the path until temp->operator_out or temp->equal_op_out, if temp->place_ptr exists, then the place's stateinputs are checked or the place inputs are traced back and checked for the state where the input is generated n compared withcontrol_st->state_node.
	
	*depth_tmp = *temp;
	while(depth_tmp){
	
		if(depth_tmp->operator_out){
		
			//function to search the end node of the current basicblock which should match with temp n it returns endnode
			Search_end_node_BasicBlock(depth_tmp , datablock, endnode,controlnode);
			if(endnode){
				endnode->operator_out = new Operate_op;
				Initialize_structures(NULL, NULL,NULL,endnode->operator_out,NULL,NULL);
				Insert_inputs_outputs(endnode->operator_out , endnode,depth_tmp->operator_out->output_value);
				//if(temp == startnode) 
					//	datablock->first_OperTree_node = endnode->operator_out;
					//else
				depth_tmp = depth_tmp->operator_out->output_value;
				node_down=true;
				if(controlnode){
					if(!controlnode->bb_ptr) controlnode->bb_ptr = datablock;
					else Insert_in_BasicBlock_list(controlnode , datablock);
					controlnode->control_out->operator_out = endnode->operator_out;
				}
			}
			else node_down = false;
			
		}
	//EDITING HERE!  continue with the other options of temp, and think if you should go depth wise or consider all the branches of temp at once
	//first, insert one depth wise path, and then come back to temp and go depthwise in anothe branch
		if(!node_down && depth_tmp->equal_op_out){
			Search_end_node_BasicBlock(depth_tmp,datablock,endnode,controlnode);
			if(endnode){
				endnode->equal_op_out = new Equal_to_op;
				Initialize_structures(NULL, NULL,NULL,NULL,endnode->equal_op_out,NULL);
				endnode->equal_op_out->rhs_value = endnode;
				endnode->equal_op_out->lhs_value = new DeclareData;
				assign_value(endnode->equal_op_out->lhs_value , depth_tmp->equal_op_out->lhs_value);
				
				depth_tmp = depth_tmp->equal_op_out->lhs_value;
				node_down=true;
				if(controlnode){
					if(!controlnode->bb_ptr) controlnode->bb_ptr = datablock;
					else Insert_in_BasicBlock_list(controlnode , datablock);
					controlnode->control_out->equal_op_out = endnode->equal_op_out;
				}
			}
			else node_down = false;
		}
		if(!node_down && depth_tmp->place_ptr){
			//here we check if the place's state input if its the same as control_st->state_node OR check the place's placeinput by tracing it back n compare wth the state
			tmp_place = depth_tmp->place_ptr;
			while(tmp_place){
			//first check for the state inputs
				tmpdata = tmp_place->state_place_input;
				stateflag=false;
				//if only the state input of this place matches with the control_st->state_node
				while(tmpdata){
					if(!strcmp(tmpdata->name , control_st->state_node->state_name->name)){
						stateflag=true;
						break;
					}
					else tmpdata = tmpdata->next_n;
				}
				//now check for the place control inputs which is not equal to depth_tmp
				if(!stateflag){
					tmpdata = tmp_place->first_place_input;
					while(tmpdata){
						//only if the tmpdata is not the same as the flow input to the transition, only control inputs will be checked here
						if(strcmp(tmpdata->name , tmp_place->first_trans_node->data_node->assignment_graph->rhs_value->name)){
							Trace_back_node(tmpdata , tmpst);
							if(!strcmp(tmpst->state_name->name , control_st->state_node->state_name->name)){
								stateflag = true;
								break;
							}
						}
						if(!stateflag) tmpdata = tmpdata->next_n;
					}
				}
				//now insert in BB again as equalopout
				if(stateflag){
					Search_end_node_BasicBlock(depth_tmp , datablock,endnode,controlnode);
					
					if(endnode){
						tmp_equal= new Equal_to_op;
						Initialize_structures(NULL, NULL,NULL,NULL,tmp_equal,NULL);
						tmp_equal->rhs_value = endnode;
						tmp_equal->lhs_value = new DeclareData;
						assign_value(tmp_equal->lhs_value, tmp_place->first_trans_node->output_var);
						node_down = true;
						if(!endnode->equal_op_out)
							endnode->equal_op_out = tmp_equal;
						else Insert_in_equalto_list(NULL,endnode , tmp_equal);
						
						if(controlnode){
							if(!controlnode->bb_ptr) controlnode->bb_ptr = datablock;
							else Insert_in_BasicBlock_list(controlnode , datablock);
							controlnode->control_out->equal_op_out = tmp_equal;
						}
					}
					
					
				}
				// this part is for exploring each place connected to the depth_tmp, thus this function is called recursively
				if(tmp_place->next_place){
					Insert_path_in_BasicBlock(control_st,datablock, tmp_place->first_trans_node->output_var);
					tmp_place = tmp_place->next_place;
				}
				else tmp_place=NULL;
			} //end of while place
			
			depth_tmp = tmp_place->first_trans_node->output_var;
		}
		if(!node_down && depth_tmp->transition_out){
			//this is only for clocked transitions
			Search_end_node_BasicBlock(depth_tmp , datablock,endnode,controlnode);
			if(endnode){
				 tmp_equal = new Equal_to_op;
				 Initialize_structures(NULL, NULL,NULL,NULL,tmp_equal,NULL);
				 tmp_equal->rhs_value = endnode;
				 tmp_equal->lhs_value = new DeclareData;
				 assign_value(tmp_equal->lhs_value , depth_tmp->transition_out->output_var);
				 node_down = true;
				 if(!endnode->equal_op_out)
				 	endnode->equal_op_out = tmp_equal;
				 else Insert_in_equalto_list(NULL,endnode, tmp_equal);
				 
				 if(controlnode){
					if(!controlnode->bb_ptr) controlnode->bb_ptr = datablock;
					else Insert_in_BasicBlock_list(controlnode , datablock);
					controlnode->control_out->equal_op_out = tmp_equal;
				}
			}
			else node_down=false;
		}
		if(!node_down && depth_tmp->comparator_out){
			stateflag = false;
			tmp_comp = depth_tmp->comparator_out;
			while(tmp_comp){
				// comparator conditions may be multiple, do similar as place condition
				tmpst = tmp_comp->state_condition;
				if(tmpst && !strcmp(tmpst->state_name->name , control_st->state_node->state_name->name))
					stateflag = true;
					
				if(!stateflag){
					//for comparator, only the condition value's state should be checked and not the lhs_compare because that would be produced before reaching here
					tmpst=NULL;
					tmpdata = tmp_comp->condition_value;
					Trace_back_node(tmpdata , tmpst);
					if(!strcmp(tmpst->state_name->name , control_st->state_name->name))
						stateflag= true;
				}
				if(stateflag){
					//when its a comparator, this part should be made as a control signal
					
					Search_end_node_BasicBlock(depth_tmp , datablock , endnode,controlnode );
					if(endnode){
						//create a control block 
						tmp_control = new Control_block;
						Initialize_nodes(NULL,NULL,NULL,tmp_control,NULL,NULL);
						tmp_control->control_in_from_dfg = endnode;
						tmp_control->control_compare_node = new Compare_operator;
						Initialize_nodes(NULL,tmp_control->control_compare_node,NULL,NULL,NULL,NULL);
						//now copy the details of depth_tmp->comparator_out to the control_Compare_node
						tmp_control->control_compare_node->lhs_compare = endnode;
						tmp_control->control_compare_node->opsymbol = tmp_comp->opsymbol;
						tmp_control->control_compare_node->value_compare = tmp_comp->value_compare;
						tmp_control->control_out = new DeclareData;
						assign_value(tmp_control->control_out , tmp_comp->value_out);
						if(!endnode->comparator_out) endnode->comparator_out = tmp_control->control_compare_node;
						else insert_in_operator_list(endnode , NULL,NULL,false,tmp_control->control_compare_node,true);
						
						node_down=true;
						//either comparator->state_condition or comparator->condition_value one of them will b valid
						//this part only for state_condition
						if(tmp_comp->state_condition){
							if(!strcmp(tmp_comp->state_condition->state_name->name , control_st->state_node->state_name->name)){
								if(!control_st->result_control) control_st->result_control = tmp_control;
								//if(!tmp_control->control_in) tmp_control->control_in = control_st;
								else Insert_in_child_list(control_st->result_control , tmp_control);
								if(!tmp_control->control_in) tmp_control->control_in = control_st;
								else Insert_in_child_list(tmp_control->control_in, control_st);
								
							}
							else if(Search_state_from_controlnode_list(tmp_comp->state_condition , first_control_node,prev_control)){
								if(!prev_control->result_control) 
									prev_control->result_control = tmp_control;
								else 
									Insert_in_child_list(prev_control->result_control, tmp_control);
								if(!tmp_control->control_in) 
									tmp_control->control_in = prev_control;
								else 
									Insert_in_child_list(tmp_control->control_in , prev_control);
								
							}
								
						}
						// this part for if there is condition_value instead of state_condition(ifcondition_var)
						else if(tmp_comp->condition_value){
							//this is an ifcondition_var, thus this can be only a wire, and is traced only in control blocks
							if(Trace_back_control_nodes(tmp_comp->condition_value , control_ret)){
							//assuming this function finds the control_ret whose output is the same as tmop_comp->condition_Value
								if(!control_ret->result_control) control_ret->result_control = tmp_control;
								else Insert_in_child_list(control_ret->result_control,tmp_control);
								//attach the comparator from the prev_control's control_out
								if(!control_ret->control_out->comparator_out) 
									control_ret->control_out->comparator_out = tmp_control->control_compare_node;
								else 
									insert_in_operator_list(control_ret->control_out , NULL,NULL,false,tmp_control->control_compare_node,true);
							}
						}
						//no need of controlnode here
						
					}
				}
				tmp_comp = tmp_comp->next_comparator;
			}
		
		}
		if(!node_down && depth_tmp->signal_selector_out){
			stateflag=false;
			tmp_signal = depth_tmp->signal_selector_out;
			while(tmp_signal){
			
				if(tmp_signal->state_in_signal && !strcmp(tmp_signal->state_in_signal->state_name->name , control_st->state_node->state_name->name))
					stateflag=true;
				if(!stateflag){
					tmpdata = tmp_signal->in_signal_list;
					while(tmpdata){
						Trace_back_node(tmpdata , tmpst,first_state);
						if(!strcmp(tmpst->state_name->name , control_st->state_node->state_name->name)){
							stateflag=true;
							break;
						}
						else tmpdata = tmpdata->next_n;
					}
				}
				if(stateflag){
					tmpdata = tmp_signal->in_signal_list;
					while(tmpdata){
						Search_end_node_BasicBlock(depth_tmp , datablock,endnode,controlnode);
						if(endnode){
							node_down = true;
							if(tmpdata == tmp_signal->in_signal_list){
						
								tmp_control = new Control_block;
								Initialize_nodes(NULL,NULL,NULL,tmp_control,NULL,NULL);
								tmp_control->control_in_from_dfg = endnode;
								tmp_control->signal_select_node = new Signal_selector;
								Initialize_nodes(tmp_control->signal_select_node,NULL,NULL,NULL,NULL,NULL);
							}
							//if the incoming signal tmpdata is generated from a controlnode
							else if(controlnode){
								controlnode->control_out->signal_selector_out = tmp_control->signal_select_node;
								tmp_control->control_in = controlnode;
							}
							// for the rest of the signals
							else{
								Insert_var_list(tmp_control->control_in_from_dfg , endnode);
								endnode->signal_selector_out = tmp_control->signal_select_node;
							}
						}
						else if(Trace_back_control_nodes(tmpdata , control_ret){
							control_ret->control_out->signal_selector_out = tmp_control->signal_select_node;
							tmp_control->control_in = control_ret;
						}
						tmpdata = tmpdata->next_n;
					}
				
				}
				tmp_signal = tmp_signal->next_selector;
			}
		
		} //end of if
		
		
	}
}while(temp);


}


//EDITING HERE
// the functions to be written: Trace_back_node , Search_end_node_BasicBblock , Trace_back_control_nodes

//this function is to trace back vartosearch in order to find the state(ret_state) which generated it
//the flag state is to indicate if this function is called from outside(true), or called recursively inside(false)
//the tmpvar is in the beginning a statevariable but it can be replaced by a normal variable, thus conditions are stated accordingly

//while tracing top-to-bottom, we only pursue the control flow inputs to the place, and not the dataflow inputs because, in that case, you have to check the state of the
//control flow inputs, which anyways will be checked during the outer while loop of the tmpstate
void Trace_back_node(DeclareData *vartosearch, State_var*& ret_state,State_var *first_state,State_var *state_continue ,bool state){

State_var *tmpstate = NULL;
State_var *tmp_st = NULL;

if(state)
	tmpstate = first_state;
else	tmpstate = state_continue;

while(tmpstate){

	tmpvar = tmpstate->state_name;
	while(tmpvar){
		search = false;
		if(!strcmp(tmpvar->name , vartosearch->name)){
			search = true;
			ret_state = tmpstate;
		}
		if(!search && tmpvar->place_ptr){
			tmp_place = tmpvar->place_ptr;
			while(tmp_place){
				//first check all the place inputs(which are not equalto the rhs value of the assignment_graph) and state inputs if they r equal to tmpstate
				tmp_tran = tmpvar->place_ptr->first_trans_node;
				while(tmp_tran){
					if(Check_state_of_place_input(tmp_place , tmpvar , tmpstate,tmp_tran,first_state)){
						if(!strcmp(tmp_tran->output_var->name , vartosearch->name)){
							ret_state = tmpstate;
							search = true;
							break;
						}
						else{
							// this is for searching vertically tracing one transition output
							tmpvar = tmp_tran->output_var;
							continueflag = true;
							break;
						
						}
						
					}
					else continueflag=false;
					tmp_tran = tmp_tran->next_trans_node;
				} //end while tran
					
				if(search) tmp_place=NULL;
				else if(!continueflag) tmp_place = tmp_place->next_place;
				else break; //THIS is going depthwise inside
			} //endof place
			if(!search && continueflag) continue;		//THIS is going depthwise inside
		}
		
		if(!search && tmpvar->operator_out){
			tmpvar = tmpvar->operator_out;
			search = true;
			continue;
		}
		if(!search && tmpvar->equal_op_out){
			tmpvar = tmpvar->equal_op_out->lhs_value;
			search = true;
			continue;
		}
		//only control nodes mustbe depthwise searched
		//here, even state_name can have this option
		if(!search && tmpvar->comparator_out){
			//EDITING HERE
			//check for the state condition and then pass the output of this comparator
			if(tmpvar->comparator_out->state_condition){
				tmp_st = tmpvar->comparator_out->state_condition;
				while(tmp_st){
					if(!strcmp(tmpstate->state_name->name , tmpvar->comparator_out->state_condition->state_name->name)){
						tmpvar = tmpvar->comparator_out->value_out;
						search = true;
						break;
					}
					tmp_st = tmp_st->next_state;
				}
			}
			else
				search = false;
		}
		if(!search && tmpvar->signal_selector_out){
			if(tmpvar->signal_selector_out->state_in_signal){
				tmp_st = tmpvar->signal_selector_out->state_in_signal;
				while(tmp_st){
					if(!strcmp(tmp_st->state_name->name , tmpstate->state_name->name)){
						tmpvar = tmpvar->signal_selector_out->out_signal;
						search=true;
						break;
					}
					tmp_st = tmp_st->next_state;
				}
			}
			else search = false;
		}
		else tmpvar=NULL;
		
	}
	tmpstate = tmpstate->next_state;
}
	
	

}

//this function first checks if placenode has state input or not. if yes, check to match with statenode, if not then check the place inputs, 
//if nodetocheck matches with the rhs value of the tran then, 

bool Check_state_of_place_input( Place_block *placenode , DeclareData *nodetocheck , State_var *statenode , Transition_block *tran,State_var *first_state){

DeclareData *tmpnode=NULL;
bool search=false;

//first: check the nodetocheck is a state name or not
//second: if yes, then send search is true, since it has to be the same as statenode
//if no, check for the state input if it exists and check if the state input is the same as statenode
// if no, then check for node if its same as rhs value of assignment graph
//if yes, then search is false
//if no, then search is true since its implied its from the same state as statenode

if(Search_var_InStateList(nodetocheck, first_state))
	search = true;
	
else if( placenode->state_place_input && !strcmp(placenode->state_place_input->name , statenode->state_name->name))
	search = true;

else if(strcmp(nodetocheck->name , tran->data_node->assignment_graph->rhs_value->name))
	search = true;
	
else search = false;

return search;

}




//this function traces in a depth-search manner from start_node to the node which is connected to a particular state(ret_state)
//this function
bool Trace_depthwise_node( DeclareData *start_node, State_var *first_state,State_var*& ret_state){

DeclareData *tmpstate=NULL;
State_var *tmps=NULL;
DeclareData *tmp=NULL;
bool search;
bool success=false;
	
	tmp = start_node;
	tmps= new State_var;
	Initialize_nodes(NULL,NULL,tmps);
	while(tmp){
		search=true;
		if(tmp->place_ptr){
			tmpstate = tmp->place_ptr->state_place_input;
			while(tmpstate){
				if(tmpstate->prev_n){
					if(Search_var_from_statelist(tmpstate,ret_state,false)){
						tmps->next_state = new State_var;
						Initialize_nodes(NULL,NULL,tmps->next_state);
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
				Trace_back_node(tmpstate , ret_state,first_state);
			}
			else 
				ret_state = tmps;
			//else ret_state=NULL;
			break;
							
		}
		 else if( tmp->operator_out){
			tmp = tmp->operator_out->output_value;
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
			if(tmp->comparator_out->state_condition){
				ret_state = tmp->comparator_out->state_condition;
				search=true;
				break;
			}
			//if there is no state condition, then trace the input of this comparator and check which state it is generated, and it returns ret_state
			else if(Trace_back_node(tmp->comparator_out->lhs_compare,ret_state,first_state)){
				search=true;
				break;
			}
			
			else
				tmp = tmp->comparator_out->value_out;
		}
		else if(tmp->equal_op_out){
			tmp = tmp->equal_op_out->lhs_value;
		}
		
		else tmp=NULL;
	
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
	if(!strcmp(tmp->state_node->state_name->name,searchnode->state_name->name)){
		flag = true;
		control_ret = tmp;
		break;
	}
	else flag=false;
	tmp = tmp->next_control_block;
}

return flag;


}

//thisfunction is to insert a child node in the list of controlnode->control_in or controlnode->result_control
void Insert_in_child_list( Control_block *parentlist , Control_block *childnode){

Control_block *tmp=NULL;
DeclareData *tmp=NULL;

//if(result_control){
	//this is only for the non-state nodes getting connected from the state nodes
	for(tmp = parentlist ; tmp->next_control_block!=NULL; tmp=tmp->next_control_block);
	tmp->next_control_block = childnode;
	childnode->next_control_block=NULL;
	childnode->prev_control_block = tmp;
//}



}





//function to assign values of a control block's state_node
void assign_controls(State_var *nodeto, State_var *nodefrom){


nodeto->state_name = nodefrom->state_name;
nodeto->next_state=NULL;
nodeto->prev_state=NULL;
nodeto->signal_selector_out=NULL;

}

void Insert_in_BasicBlock_list(Control_block *ctrlnode , Basic_block *bbnode){

Basic_block *tmp=NULL;

for(tmp = ctrlnode->bb_ptr , tmp->next_block!=NULL; tmp = tmp->next_block);
tmp->next_block = bbnode;
bbnode->next_block = NULL;
bbnode->prev_block=tmp;

}












