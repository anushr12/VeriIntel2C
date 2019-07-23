#include <iostream>
#include <fstream>
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


Path_node *node_list[50];
Operate_op *comparator_nodelist[4];
extern State_var *first_state;

using namespace std;

#ifdef VERIFIC_NAMESPACE
using namespace Verific ;
#endif

// algorithm to obtain the path of operations for FOR loop initial condition and operations inside FOR loop


void search_graph_FORloop(Graph_node *graph_first_node , State_var *first_state , Place_block *first_place_node){

bool caseflag=false;
bool compsearch=false;
bool varflag=true;
bool create=false;
Transition_block *transearch=NULL;
Transition_block *prevtr=NULL;
DeclareData *prevout=NULL;
Operate_op *operator_comp=NULL;
DeclareData *iteration_var=NULL;
int num,nodenumber=0,i=0;

// to attach the async reset nodes to the outputs of the nodes with cond var
Attach_condvar_to_node(first_place_node);

//for searching switch case block of verilog
num=1;
caseflag = Search_transition(first_place_node , transearch,iteration_var,operator_comp, num,false,NULL);
//if no switch case,search for the comparator and the input to the input of the node before comparator, will be the iteration variable

//prepare memory for the list of comparators
/*for(i=0;i<4;i++){
	comparator_nodelist[i]=new Operate_op;
	Initialize_structures(NULL,NULL,NULL,comparator_nodelist[i],NULL,NULL);
}*/



//obrain the place input of this transition node
if(caseflag){
	iteration_var = transearch->own_place_ptr->first_place_input;
	//further check if the iteration var is connected to a comparator or not and send back the operator node
	
	//check how many comparators are in the module
//	caseflag = Search_var_from_graph(NULL,iteration_var , prevtr,prevout,varflag);
	if(varflag && caseflag){ //meaning there  1 comparator
		num=2;
		if(Search_transition( transearch->own_place_ptr , transearch, iteration_var ,operator_comp, num,false,NULL))
			{
				if(operator_comp)
				{
			
					Create_search_list(iteration_var,operator_comp,first_place_node , nodenumber);
					//print this list of operations to a new source file
					//Create_source_code(condition , operator_comp);
					//num=0;delete_null_nodes(num);
					create = Create_loop_operations_list(iteration_var,operator_comp,first_place_node,nodenumber);
					
				}	
		
			}//Traverse_to_node(operator_compare
	}	
		
	else if(!varflag && caseflag) {//meaning there is more than 1 comparator
	
		i=0;
		while(comparator_nodelist[i] && comparator_nodelist[i]->op_type){
			
		
		
		
		}
	
	
	}
}

else if(!caseflag){

	//if there is no switch case
	//search for the comparator node and the input to the input of the comparator is the iteration variable
	transearch = first_place_node->first_trans_node;
	varflag = true;
	while(transearch){
	//	caseflag = Search_var_from_graph(NULL,transearch->output_var,prevtr,prevout,varflag);
		if(caseflag){
			compsearch=true;
			break;
		}
		transearch = transearch->next_trans_node;
	}
	
	if(compsearch) iteration_var = transearch->output_var; // the variable from where the comparator is searched
	
	if(compsearch && !varflag){ //this case for more than 1 comparator
	
		i=0;
		while(comparator_nodelist[i]){
		//	iteration_var = Get_var_from_comparator(comparator_nodelist[i]);
			Create_search_list(iteration_var,comparator_nodelist[i],first_place_node , nodenumber);
			
			create = Create_loop_operations_list(iteration_var,comparator_nodelist[i],first_place_node,nodenumber);
			i++;
		}
	
	}
	else if(compsearch && varflag){
	
		//iteration_var = Get_var_from_comparator(comparator_nodelist[0]);
		Create_search_list( iteration_var , comparator_nodelist[0] , first_place_node , nodenumber);
		
		create = Create_loop_operations_list(iteration_var,comparator_nodelist[0],first_place_node,nodenumber);
	
	}
}



}


// to find the iteration var connected with the comparator
DeclareData *Get_var_from_comparator(Operate_op *comp){

Operate_op *tmp=NULL;
DeclareData *var = NULL;

	if(comp->op1->data_type!=integer){
	
		tmp = comp->op1->operator_in;
		if(tmp && tmp->op_type == '+'){
			if(tmp->op1->data_type!=integer && tmp->op1->equal_op_out) 
				var = tmp->op1->equal_op_out->rhs_value;
			
			else if(tmp->op2->data_type!=integer && tmp->op2->equal_op_out) 
				var =  tmp->op2->equal_op_out->rhs_value;
			
		}
	}
	else if(comp->op2->data_type!=integer){
	
		tmp = comp->op2->operator_in;
		if(tmp && tmp->op_type == '+'){
			if(tmp->op2->data_type!=integer && tmp->op2->equal_op_out) 
				var = tmp->op2->equal_op_out->rhs_value;
			
			else if(tmp->op2->data_type!=integer && tmp->op2->equal_op_out) 
				var =  tmp->op2->equal_op_out->rhs_value;
			
		}
	}
	
return var;

}





//function to create path of operations which are part of FOR loop
bool Create_loop_operations_list(DeclareData *iteration_var, Operate_op *operator_comp, Place_block *first_place_node,int num){

int i;
int caseselect = 2;
bool search=false;
bool create = false;
bool store=false,flag=false,iterationflag=true,nextflag=false;
DeclareData *var=NULL;
DeclareData *tmpv=NULL;
Operate_op *tmpo=NULL;
Operate_op *opsearch=NULL , *opsearch_s=NULL;
DeclareData *tempvar=NULL;
Transition_block *tmpt=NULL;
Transition_block *tran=NULL;
Equal_to_op *tmpe=NULL;
DFG_block *tmpd=NULL;
Place_block *tmp=NULL;
Place_block *place_n=NULL;
Operate_op *op_return=NULL;
Transition_block *node_tran=NULL;

// to check the taken path from iteration var in the previous search for loop condition
if(node_list[0]->varnode==iteration_var){
	if(node_list[1]->varnode) tmpv = node_list[1]->varnode;
	else if(node_list[1]->opnode) tmpo = node_list[1]->opnode;
	else if(node_list[1]->trannode) tmpt = node_list[1]->trannode;
	else if(node_list[1]->equalnode) tmpe = node_list[1]->equalnode;
	else if(node_list[1]->dfgnode) tmpd = node_list[1]->dfgnode;
	else if(node_list[1]->placenode) tmp = node_list[1]->placenode;
}


for(i=num;i<50;i++){
	node_list[i]=new Path_node;
	Initialize_structures(NULL,NULL,NULL,NULL,NULL,node_list[i]);
}

var = iteration_var;
i=num;

while( iterationflag && i<50 && var){

iterationflag=false;
nextflag=true;

	if(var->operator_out && var->operator_out!= tmpo){
		
		tempvar = var;
		opsearch = tempvar->operator_out;
		opsearch_s = opsearch;
		do{
			opsearch = opsearch_s;
			while(opsearch){
				if(opsearch->op3){
					opsearch = opsearch->op3;
					continue;
				}
		
			else if(opsearch->output_value && opsearch->output_value->name && Search_transition( first_place_node,node_tran,opsearch->output_value,op_return,caseselect,true,operator_comp)){
		
				if(nextflag)
					node_list[i++]->varnode = var;
				node_list[i++]->opnode = opsearch;
			
				iterationflag=true;
				nextflag=false;
				
				var = var->operator_out->output_value;
			}
			
			else iterationflag=false;
			opsearch = opsearch->op3;
			}
			opsearch_s = opsearch_s->next_oper;
			
		}while(opsearch_s);
	
	}
	if(!iterationflag && var->equal_op_out && var->equal_op_out!=tmpe){
	
		if(Search_transition(first_place_node,node_tran,var->equal_op_out->lhs_value,op_return,caseselect,true,operator_comp)){
		
			if(nextflag)
				node_list[i++]->varnode = var;
			node_list[i++]->equalnode = var->equal_op_out;
			
			iterationflag=true;
			nextflag=false;
			
			var = var->equal_op_out->lhs_value;
		}
		else iterationflag=false;
	
	}
	if(!iterationflag && var->transition_out && var->transition_out!=tmpt){
	
		if(Search_transition(first_place_node , node_tran,var->transition_out->output_var,op_return,caseselect,true,operator_comp)){
		
			if(nextflag) node_list[i++]->varnode = var;
			node_list[i++]->trannode = var->transition_out;
			
			iterationflag=true;
			nextflag=false;
			var = var->transition_out->output_var;
		}
		else iterationflag=false;

	}
	
	if(!iterationflag && var->place_ptr && var->place_ptr!=tmp){
	
		if(Search_placeInput(var->place_ptr , operator_comp)){
			if(nextflag) node_list[i++]->varnode = var;
			node_list[i++]->placenode = var->place_ptr;
			search=true;
			break;
		}
		iterationflag=true;
		tran = var->place_ptr->first_trans_node;
		
		while(tran){
			if(Search_transition(tran->own_place_ptr , node_tran,tran->output_var,op_return,caseselect,true,operator_comp)){
				if(nextflag)
					node_list[i++]->varnode = var;
				node_list[i++]->placenode = var->place_ptr;
				node_list[i++]->trannode = tran;
				store=true; break;
			}
			tran = tran->next_trans_node;
		}
		nextflag=false;
		if(store) var = tran->output_var;
		else iterationflag=false;
	
	}

	if(search) var=NULL;

}

if(i==num) create = false;
else create = true;

return create;

}


//two cases:first case: to search for a switch case block and return that transition block
//second case: to search for the path from iteration_var to the comparator node, and for the path from iteration_var to place node having input of comparator output
bool Search_transition(Place_block *place_n , Transition_block*& node_tran ,DeclareData *iteration_var,Operate_op*& op_return, int num,bool loopsearch,Operate_op *operator_compare){

Transition_block *transnode=NULL;
Transition_block *tran=NULL;
Operate_op *opnext=NULL;
Operate_op *opnext_s=NULL;
Operate_op *opsearch=NULL;
Operate_op *opsearch_s=NULL;
bool returnflag=false;
DeclareData *var=NULL;
DeclareData *var_s=NULL;
DeclareData *tempvar=NULL;
bool assignflag = false;

//if(place_n->next_trans_node){

	transnode = place_n->first_trans_node;

	
		
	switch(num){
		
		case 1: //to search a switch-case verilog block
		{
		
		while(transnode){
		
		if(transnode->data_node->condition_op && transnode->data_node->condition_op->switchcase){
			Insert_datainput_in_placelist(transnode,assignflag); // connect the inputs of the condition_op as place_inputs and connect them to the previous outvar's
			if(assignflag){
			node_tran = transnode;
			returnflag=true;
			break;
			}
		}
		else if(transnode->outgoing_external_place && Search_transition(transnode->outgoing_external_place, node_tran,iteration_var,op_return,num,false,operator_compare)){
			//node_tran=transnode;
			returnflag=true;
			break;
		}
		
		else if(transnode->outgoing_external_dfg || transnode->output_var){
		//search for the external dfg
			if(transnode->outgoing_external_dfg) var_s = transnode->outgoing_external_dfg->output;
			else var_s = transnode->output_var;
			
			var = var_s;
			while(var && var->equal_op_out){
			if(var->place_ptr && Search_transition(var->place_ptr, node_tran,iteration_var,op_return,num,false,operator_compare)){
				returnflag=true;
				break;
			}
			else var = var->equal_op_out->lhs_value;
			}
			
			
			//search for operations below the dfg
			if(!returnflag && var_s->operator_out){
			var_s = var_s->operator_out->output_value;
			var = var_s;
			while(var){
				if(var->place_ptr && Search_transition(var->place_ptr, node_tran,iteration_var,op_return,num,false,operator_compare)){
				returnflag=true;
				break;
				}
				
			else if(var->operator_out) var = var->operator_out->output_value;
			else var=NULL;
			}
			
			}
			
			if(!returnflag){
			if(transnode->outgoing_external_dfg) var = transnode->outgoing_external_dfg->output;
			else var = transnode->output_var;
			
			//var=var_s;
			if(!returnflag && var->operator_out && var->operator_out->next_oper){
				opnext = var->operator_out;
				opnext_s = opnext;
				do{
				opnext = opnext_s;
					while(opnext){
						if(opnext->op3){
						opnext = opnext->op3;
						continue;
						}
						else if(opnext->output_value && opnext->output_value->place_ptr && Search_transition(opnext->output_value->place_ptr, node_tran,iteration_var,op_return,num,false,operator_compare)){
							returnflag=true;
							break;
						}
						opnext = opnext->op3;
					}
					if(!returnflag && opnext_s) opnext_s = opnext_s->next_oper;
					else opnext_s = NULL;
				}while(opnext_s);
			
			}
			}
			
			}
			
		if(!returnflag && place_n->next_trans_node) transnode = transnode->next_trans_node;
		else transnode=NULL;
		}		
		
		break;
		}
		case 2: //search for comparator dfg node with iteration_var
		{
			//if(!transnode->own_place_ptr->first_place_input->next_n){
				
				if(iteration_var->operator_out){
				
					
					
					tempvar = iteration_var;
					opsearch = tempvar->operator_out;
					opsearch_s = opsearch;
					do{
						opsearch = opsearch_s;
						while(opsearch){
							
							if(!loopsearch && (opsearch->op_type == '<' || opsearch->op_type == '>')){
					 		op_return = opsearch;
					 		//node_tran = transnode;
							returnflag = true;
							break;
							}
							
						if(opsearch->output_value){
							
							if(!loopsearch && Search_transition(place_n,node_tran,opsearch->output_value,op_return,num,false,operator_compare))
							//if(opsearch->output_value->equal_op_out && Search_transition(place_n,node_tran,opsearch->output_value->equal_op_out->lhs_value,op_return,num))
							{returnflag=true;break;}
							
							else if(loopsearch && Search_transition(place_n,node_tran,opsearch->output_value,op_return,num,true,operator_compare))
							{returnflag=true;break;}
						
							else opsearch = opsearch->output_value->operator_out;
						}
						else opsearch = opsearch->op3;
						}
					if(!returnflag) opsearch_s=opsearch_s->next_oper;
					else opsearch_s=NULL;
					}while(opsearch_s);
				
				}
				if(!returnflag && iteration_var->equal_op_out){
					
					var_s = iteration_var->equal_op_out->lhs_value;
					var = var_s;
					while(var){
						if(var->equal_op_out){
						var = var->equal_op_out->lhs_value;
							if(!loopsearch && var && Search_transition(place_n,node_tran,var,op_return,num,false,operator_compare))
							{ returnflag=true;break;}
							else if(loopsearch && var && Search_transition(place_n,node_tran,var,op_return,num,true,operator_compare))
							{ returnflag=true;break;}
							else
							continue;
						}
						/*else if(var->operator_out && Search_transition(place_n, node_tran,var ,op_return,num)){
							returnflag=true;
							break;
						}*/
						else if(!loopsearch && Search_transition(place_n,node_tran,var,op_return,num,false,operator_compare)){
							returnflag=true;
							break;
						}
						else if(loopsearch && Search_transition(place_n,node_tran,var,op_return,num,true,operator_compare)){
							returnflag = true;
							break;
						}
							
						else if(var->operator_out) var = var->operator_out->output_value;
						else var=NULL;
					}
				}
				if(!returnflag && iteration_var->place_ptr){
					tran = iteration_var->place_ptr->first_trans_node;
					
					if(loopsearch && Search_placeInput(iteration_var->place_ptr , operator_compare)){
						//place_search = iteration_var->place_ptr;
						returnflag=true;
						break;
					}
					
					
					while(tran){
						if(!loopsearch && tran->output_var && Search_transition(place_n , node_tran,tran->output_var,op_return,num,false,operator_compare)){
							returnflag=true;
							node_tran = tran; //this only is for special case for create_search_list 
							break;
						}
						else if(loopsearch && tran->output_var && Search_transition(place_n , node_tran,tran->output_var,op_return,num,true,operator_compare)){
							returnflag=true;
							break;
						}
					tran = tran->next_trans_node;
					}
				}
				if(!returnflag && iteration_var->transition_out){
					if(!loopsearch && iteration_var->transition_out->output_var && Search_transition(place_n,node_tran, iteration_var->transition_out->output_var,op_return,num,false,operator_compare)){
						returnflag=true;
						node_tran = iteration_var->transition_out;
						break;
					}
					else if(loopsearch && iteration_var->transition_out->output_var && Search_transition(place_n , node_tran,iteration_var->transition_out->output_var,op_return,num,true,operator_compare)){
							returnflag=true;
							break;
						}
					
				}
		
		//}
		
		break;
		}
		
	

}
return returnflag;
}

//function to search if opsearch is in the list of the comparators
bool Search_comp_from_comparator_list(Operate_op *opsearch,int num,bool select){

int i=0;
bool flag = false;

if(select && comparator_nodelist[i]){
while(comparator_nodelist[i] && comparator_nodelist[i]->op_type){
	if(comparator_nodelist[i] == opsearch){
		flag=false;
		break;
	}
	else 
	flag=true;

	//}
	i++;
}
num = i;
}

else if(!select){

	num = 0;
	flag = true;
}

return flag;

}



// to search a particular variable from the entire graph
//external call to this function varflag=false
//internal recursive call varflag = true
bool Search_var_from_graph( DeclareData *varsearch, DeclareData *vartemp,Transition_block *prevtr ,Compare_operator*& prevcomp,Signal_selector*& prev_sig,DeclareData* prevout,State_var *state,bool varflag,bool send_value ){

bool search = false;
bool flag=false;
int num=0;
//Transition_block *tran=NULL;
DeclareData *var=NULL;
DeclareData *tempvar=NULL;
Transition_block *trantmp=NULL;
//DeclareData *vartemp=NULL;
Operate_op *opsearch=NULL;
Operate_op *opsearch_s=NULL;
Place_block *tmp_place=NULL;
State_var *tmp_state=NULL;
//Compare_operator *tmpcomp=NULL;
//Signal_selector *tmpsig=NULL;

//tran = placenode->first_trans_node;

if(!varflag)
	tmp_state = first_state;
else	tmp_state = state;
	while(tmp_state){
		prevcomp=NULL;
		prev_sig=NULL;
			if(!varflag) vartemp = tmp_state->state_name;
			//vartemp = tmp_place->first_trans_node->output_var;
			while(vartemp){
				search = false;
				if(!strcmp(varsearch->name , vartemp->name)){
				
					if(send_value) prevout = vartemp;
					//if(tmpcomp) prevcomp = tmpcomp;
					//else if(tmpsig) prev_sig = tmpsig;
					search = true;
					break;
				}
				tmpcomp = NULL;
				tmpsig=NULL;
				if(!search && vartemp->comparator_out){
					
					
					//vartemp = vartemp->comparator_out->value_out;
					if(send_value) prevcomp = vartemp->comparator_out;
					vartemp = vartemp->comparator_out->value_out;
					continue;
					/*
					if(Search_var_from_graph(varsearch,vartemp->comparator_out->value_out,prevtr,prevcomp,prev_sig,prevout,tmp_state,true)){
						search = true;
						prevcomp = vartemp->comparator_out;
					}
					else vartemp = vartemp->comparator_out->value_out;
					*/
				}
			
				if(!search && vartemp->operator_out){
				
					vartemp = vartemp->operator_out->output_value;
				}	
				
				if(!search && vartemp->equal_op_out){
				
					vartemp = vartemp->equal_op_out->lhs_value;
					
				}	
				if(!search && vartemp->transition_out){
					
					trantmp = vartemp->transition_out;
					while(var_tr){
						if(Search_var_from_graph(varsearch,trantmp->output_var,prevtr,prevcomp,prev_sig,prevout,tmp_state,true,send_value)){
							search=true;
							if(send_value) prev_tr = trantmp;
							break;
						}
						trantmp= trantmp->next_trans_node;
					}
					if(!search){
						vartemp = NULL;
						varflag=false;
					}
					
				}
				if(!search && vartemp->place_ptr){
				
					tmp_place = vartemp->place_ptr;
					while(tmp_place){
						var = tmp_place->first_trans_node->output_var;
						if(Search_var_from_graph(varsearch,var,prevtr,prevcomp,prev_sig,prevout,tmp_state,true,send_value)){
							search = true;
							if(send_value) prevtr = tmp_place->first_trans_node;
							break;
						}
						tmp_place = tmp_place->next_place;
					}
					if(!search){
						vartemp=NULL;
						varflag=false;
					}
					
				}
				if(!search && vartemp->signal_selector_out){
				
					if(send_value) prev_sig = vartemp->signal_selector_out;
					vartemp = vartemp->signal_selector_out->out_signal;
					continue;
				}	
				
				else{
					vartemp=NULL;
					varflag=false;
				}
	
			}
			
		tmp_state = tmp_state->next_state;
	}

//if the output is from a comparator or signal_selector only then search is true
if(send_value && (prevcomp || prev_sig)) search = true;

return search;

}




//function to create the path list for printing FOR loop condition
//searchflag in Search_transition will be false here
void Create_search_list(DeclareData *iteration_var, Operate_op *comparator,Place_block *first_place_node,int &number){

//Transition_block *trannode=NULL;
Transition_block *tran_search=NULL;
Transition_block *tran=NULL;
bool store=false,flag=false,iterationflag=true,nextflag=false;
Operate_op *op_return=NULL;
Operate_op *operator_compare=NULL;
int i=0;
DeclareData *var=NULL;
int num=2;

//trannode = first_place_node->first_trans_node;
//node_list = new Path_node[10];
var = iteration_var;
//start from the iteration_var and end until you find the comparator dfg node

for(i=0;i<50;i++){
node_list[i]=new Path_node;
Initialize_structures(NULL,NULL,NULL,NULL,NULL,node_list[i]);
}

i=0;
while(i<50 && var && iterationflag){
	iterationflag=false;
	nextflag=true;
	if(var->operator_out && Search_transition(first_place_node,tran_search,var,op_return,num,false,operator_compare)){
	
	//node_list is the pointe to an array of struct pointers
		if(nextflag)
			node_list[i++]->varnode = var;
		
		iterationflag=true;
		nextflag=false;
			
	 	if(var->operator_out==comparator){
	 		node_list[i++]->opnode = var->operator_out;
			//delete node_list[i];
			//node_list[i]=NULL;
			flag=true;
			break;
		}
	
	if(var->operator_out->output_value && Search_transition(first_place_node,tran_search,var->operator_out->output_value,op_return,num,false,operator_compare)){
		node_list[i++]->opnode = var->operator_out;
		var = var->operator_out->output_value;
	}
	else iterationflag=false;
	
	}
	if(!iterationflag && var->equal_op_out && Search_transition(first_place_node,tran_search,var,op_return,num,false,operator_compare)){
		
		if(nextflag)
			node_list[i++]->varnode = var;
		
		iterationflag=true;
		nextflag=false;
		
		if(var->equal_op_out->lhs_value && Search_transition(first_place_node,tran_search,var->equal_op_out->lhs_value,op_return,num,false,operator_compare)) {
			node_list[i++]->equalnode = var->equal_op_out;
			var= var->equal_op_out->lhs_value;
			
		}
		else iterationflag=false;
		/*else{
			node_list[i--]->opnode=NULL;
			node_list[i--]->varnode=NULL; 
			var = Get_previous_varnode(i,node_list);
		}*/	
		
		
	}
	if(!iterationflag && var->dfgnode_out && Search_transition(first_place_node,tran_search,var,op_return,num,false,operator_compare)){
		
		if(nextflag)
			node_list[i++]->varnode = var;
		
		iterationflag=true;
		nextflag=false;
		/*if(var->dfgnode_out->operation_graph && var->dfgnode_out->operation_graph == comparator){
			
			node_list[i++].opnode=var->dfgnode_out->operation_graph;
			flag=true;
			break;
		 }*/
		//if(var->dfgnode_out->output && Search_transition(first_place_node, tran_search,var->dfgnode_out->output,op_return,num))
			if(var->dfgnode_out->output && Search_transition(first_place_node,tran_search,var->dfgnode_out->output,op_return,num,false,operator_compare)){
				node_list[i++]->dfgnode = var->dfgnode_out;
				var = var->dfgnode_out->output;
			}
			else iterationflag=false;
		/*else{
			node_list[i--]->dfgnode=NULL;
			node_list[i--]->varnode=NULL; 
			var = Get_previous_varnode(i,node_list);//get the previous path_listnode's attached outputvar
		 	
		 }*/
		 
	
	}
	if(!iterationflag && var->place_ptr){
		
		
			//node_list[i++]->varnode= var;
		node_list[i++]->placenode = var->place_ptr;
		tran = var->place_ptr->first_trans_node;
		iterationflag=true;
		i++;
		while(tran){
			if(Search_transition(var->place_ptr,tran_search,tran->output_var,op_return,num,false,operator_compare))
				{
				if(nextflag) node_list[i++]->varnode = var;
				node_list[i++]->trannode = tran; 
				store=true;break;}
				
			//else if(tran->output_var && Search_transition(first_place_node,tran_search,tran->output_var,op_return,num))
			//	{var = tran->output_var;break; }
				
		tran = tran->next_trans_node; 
		}
		nextflag=false;
		
		if(store && tran->output_var && Search_transition(tran->own_place_ptr, tran_search,tran->output_var,op_return,num,false,operator_compare))
			 var = tran->output_var;
		else iterationflag=false;
			
		if(!store) 
		{ 	node_list[i--]->placenode=NULL;
			delete node_list[i];node_list[i]=NULL;
			//node_list[i--]->varnode=NULL;
			//delete node_list[i];node_list[i]=NULL;
			iterationflag=false;
		}
		
	}
	if(!iterationflag && var->transition_out && Search_transition(first_place_node,tran_search,var,op_return,num,false,operator_compare)){
	
		if(nextflag)
			node_list[i++]->varnode = var;
		
		iterationflag=true;
		nextflag=false;
		
		if(var->transition_out->output_var && Search_transition(var->transition_out->own_place_ptr, tran_search, var->transition_out->output_var,op_return,num,false,operator_compare)){
			 node_list[i++]->trannode = var->transition_out;
			 var = var->transition_out->output_var;
		}
		else iterationflag=false;
	}
	
	
}

number = i;
if(flag) delete_null_nodes(i); //for deleting the null nodes in the node_list

}



//function to search if the output of operator is a place input to placetmp
bool Search_placeInput(Place_block *placetmp , Operate_op *operator_compare){

bool search=false;
DeclareData *var=NULL;

var = placetmp->first_place_input;

while(var){

	if(!strcmp(var->name, operator_compare->output_value->name))
		{search = true;break;}
	else
		search =false;
	var = var->next_n;
}

return search;

}


/*
DeclareData *Get_previous_varnode(int j, Path_node **list){

DeclareData *var=NULL;

if(list[j]->opnode)
	{ var = list[j--]->varnode;}
	
else if(list[j]->equalnode)
	{var = list[j--]->varnode;}
	
else if(list[j]->dfgnode)
	{var = list[j--]->varnode;}
	
else if(list[j]->placenode)
	{var = list[j--]->varnode;}
	
	
return var;
	
}
*/


void delete_null_nodes(int i){

//int i=0;

while(i<50 && node_list[i]){

	//if(!node_list[i]->opnode && !node_list[i]->varnode && !node_list[i]->placenode && !node_list[i]->trannode && !node_list[i]->equalnode && !node_list[i]->dfgnode){
		
		delete node_list[i];
		node_list[i]=NULL;
		//node_list[i] = node_list[i+1];
	//}
i++;
}


}

/*
void Create_source_code(bool cond , Operate_op *opcompare){

ofstream myfile;
int i=0;


myfile.open("Csource.c");

if(myfile.is_open()){
	
	//the node_list always starts with the increment variable
	myfile << "#include <stdio.h>" << '\n' << "include <string.h>" << '\n' << "#include <stdlib.h>" << '\n';
	myfile << "void main(void){" << '\n' << "{" <<'\n';


if(cond){
	myfile << "for(" << node_list[i++]->varnode ;
	
	while(node_list[i]->opnode!= opcompare)
		i++;
		
	//myfile << node_list[i]->opnode->output_value << "=" << node_list[i]->opnode->op1 << node_list[i]->opnode->op_type << node_list[i]->opnode->op2;
	
	
	
		//if(node_list[i]->varnode)
		
	
			


	//}
	
}

}


}

*/


//function to attach the asynchronous reset nodes with if_cond_var to the nodes with the output having if_cond_var
void Attach_condvar_to_node(Place_block *first_place_node){

Transition_block *tmp=NULL;
State_var *statevar=NULL;
Transition_block *tran=NULL;
DeclareData *prev_out=NULL;
Transition_block *prev_tr=NULL;
Place_block *place_node=NULL;
bool flag=false;

tmp = first_place_node->first_trans_node;
//tran = tmp;

while(tmp){


		if(tmp->data_node->condition_op){
		tran = first_place_node->first_trans_node;
		flag=false;
			while( tran){
				if(Search_var_from_graph(tmp->data_node->condition_op->if_cond_var,tran->output_var,prev_tr,prev_out,false))
				{flag=true;break;}
				tran = tran->next_trans_node;
			}
			if(!flag && Search_var_from_statelist(tmp->data_node->condition_op->if_cond_var ,statevar,true)){
				flag = true;
				if(!statevar->state_name->operator_out->output_value->transition_out) statevar->state_name->operator_out->output_value->transition_out = tmp;
				}
			
			if(flag){
			if(prev_tr && !prev_tr->output_var->transition_out)
				prev_tr->output_var->transition_out = tmp;
			else if(prev_out && !prev_out->transition_out)
				prev_out->transition_out = tmp;	
			}
		}
	
tmp = tmp->next_trans_node;

}
	
}





else if(cond){

tmp = first_state;
while(tmp){
	if(tmp->state_name->operator_out && !strcmp(var->name,tmp->state_name->operator_out->output_value->name)){
		flag=true;
		svar = tmp;
		break;
	}
	tmp = tmp->next_state;
}

}

return flag;

}



















