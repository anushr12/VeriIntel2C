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


Path_node *node_list[20];

using namespace std;

#ifdef VERIFIC_NAMESPACE
using namespace Verific ;
#endif

// algorithm

void search_graph_FORloop(Graph_node *graph_first_node , State_var *first_state , Place_block *first_place_node){

bool caseflag=false;
Transition_block *transearch=NULL;
Operate_op *operator_compare=NULL;
DeclareData *iteration_var=NULL;
int num,nodenumber;


//for searching switch case block of verilog
num=1;
caseflag = Search_transition(first_place_node , transearch,iteration_var,operator_compare, num);

//obrain the place input of this transition node
if(caseflag){
	iteration_var = transearch->own_place_ptr->first_place_input;
	//further check if the iteration var is connected to a comparator or not and send back the operator node
	num=2;
	if(Search_transition( transearch->own_place_ptr , transearch, iteration_var ,operator_compare, num))
		{
			if(operator_compare)
			{
			
				Create_search_list(iteration_var,operator_compare,first_place_node , nodenumber);
				//print this list of operations to a new source file
				Create_source_code();
				//num=0;delete_null_nodes(num);
				Create_loop_operations_list(iteration_var,operator_compare,first_place_node,nodenumber);
				
				
				
				
			}	
		
		}//Traverse_to_node(operator_compare
}

}

//function to create path of operations which are part of FOR loop
void Create_loop_operations_list(DeclareData *iteration_var, Operate_op *operator_compare, Place_block *first_place_node,int num){

int i;
bool searchflag=false;
DeclareData *var=NULL;
DeclareData *tmpv=NULL;
Operate_op *tmpo=NULL;
Transition_block *tmpt=NULL;
Equal_to_op *tmpe=NULL;
DFG_block *tmpd=NULL;
Place_block *tmp=NULL;

// to check the taken path from iteration var in the previous search for loop condition
if(node_list[0]->varnode==iteration_var){
	if(node_list[1]->varnode) tmpv = node_list[1]->varnode;
	else if(node_list[1]->opnode) tmpo = node_list[1]->opnode;
	else if(node_list[1]->trannode) tmpt = node_list[1]->trannode;
	else if(node_list[1]->equalnode) tmpe = node_list[1]->equalnode;
	else if(node_list[1]->dfgnode) tmpd = node_list[1]->dfgnode;
	else if(node_list[1]->placenode) tmp = node_list[1]->placenode;
}


for(i=num;i<20;i++){
	node_list[i]=new Path_node;
	Initialize_structures(NULL,NULL,NULL,NULL,NULL,node_list[i]);
}
var = iteration_var;
i=num;
while( i<20 && var && searchflag){

 
	if(var->place_ptr && var->place_ptr != tmp){
	
		if(var!=iteration_var) node_list[i++]->varnode = var;
		node_list[i++]->placenode = var->place_ptr;
		
		tran = var->place_ptr->first_trans_node;
		while(tran)
			
		
	
	}
	


}



}



bool Search_transition(Place_block *place_n , Transition_block*& node_tran ,DeclareData *iteration_var,Operate_op*& op_return, int num){

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


//if(place_n->next_trans_node){

	transnode = place_n->first_trans_node;

	
		
	switch(num){
		
		case 1: //to search a switch-case verilog block
		{
		
		while(transnode){
		
		if(transnode->data_node->condition_op && transnode->data_node->condition_op->switchcase){
			Insert_datainput_in_placelist(transnode); // connect the inputs of the condition_op as place_inputs and connect them to the previous outvar's
			node_tran = transnode;
			returnflag=true;
			break;
		}
		else if(transnode->outgoing_external_place && Search_transition(transnode->outgoing_external_place, node_tran,iteration_var,op_return,num)){
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
			if(var->place_ptr && Search_transition(var->place_ptr, node_tran,iteration_var,op_return,num)){
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
				if(var->place_ptr && Search_transition(var->place_ptr, node_tran,iteration_var,op_return,num)){
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
						else if(opnext->output_value && opnext->output_value->place_ptr && Search_transition(opnext->output_value->place_ptr, node_tran,iteration_var,op_return,num)){
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
				
					Attach_condvar_to_node(iteration_var ,first_place_node);
					
					tempvar = iteration_var;
					opsearch = tempvar->operator_out;
					opsearch_s = opsearch;
					do{
						opsearch = opsearch_s;
						while(opsearch){
							
							if(opsearch->op_type == '<'){
					 		op_return = opsearch;
					 		//node_tran = transnode;
							returnflag = true;
							break;
							}
							
						if(opsearch->output_value){
							
							if(Search_transition(place_n,node_tran,opsearch->output_value,op_return,num))
							//if(opsearch->output_value->equal_op_out && Search_transition(place_n,node_tran,opsearch->output_value->equal_op_out->lhs_value,op_return,num))
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
					
					Attach_condvar_to_node(iteration_var ,first_place_node);
					
					var_s = iteration_var->equal_op_out->lhs_value;
					var = var_s;
					while(var){
						if(var->equal_op_out){
						var = var->equal_op_out->lhs_value;
							if(var && Search_transition(place_n,node_tran,var,op_return,num))
							{ returnflag=true;break;}
							else
							continue;
						}
						/*else if(var->operator_out && Search_transition(place_n, node_tran,var ,op_return,num)){
							returnflag=true;
							break;
						}*/
						else if(Search_transition(place_n,node_tran,var,op_return,num)){
							returnflag=true;
							break;
						}
							
						else if(var->operator_out) var = var->operator_out->output_value;
						else var=NULL;
					}
				}
				if(!returnflag && iteration_var->place_ptr){

					Attach_condvar_to_node(iteration_var ,first_place_node);
					
					tran = iteration_var->place_ptr->first_trans_node;
					
					while(tran){
						if(tran->output_var && Search_transition(place_n , node_tran,tran->output_var,op_return,num)){
							returnflag=true;
							node_tran = tran; //this only is for special case for create_search_list 
							break;
						}
					tran = tran->next_trans_node;
					}
				}
				if(!returnflag && iteration_var->transition_out){
				
					Attach_condvar_to_node(iteration_var ,first_place_node);
				
					if(iteration_var->transition_out->output_var && Search_transition(place_n,node_tran, iteration_var->transition_out->output_var,op_return,num)){
						returnflag=true;
						node_tran = iteration_var->transition_out;
						break;
					}
					
					
				}
		
		//}
		
		break;
		}
		
	

}
return returnflag;
}


//function to create the path list for printing FOR loop condition
void Create_search_list(DeclareData *iteration_var, Operate_op *comparator,Place_block *first_place_node,int number){

//Transition_block *trannode=NULL;
Transition_block *tran_search=NULL;
Transition_block *tran=NULL;
bool store=false,flag=false,iterationflag=true,nextflag=false;
Operate_op *op_return=NULL;
int i=0;
DeclareData *var=NULL;
int num=2;

//trannode = first_place_node->first_trans_node;
//node_list = new Path_node[10];
var = iteration_var;
//start from the iteration_var and end until you find the comparator dfg node

for(i=0;i<20;i++){
node_list[i]=new Path_node;
Initialize_structures(NULL,NULL,NULL,NULL,NULL,node_list[i]);
}

i=0;
while(i<20 && var && iterationflag){
	iterationflag=false;
	nextflag=true;
	if(var->operator_out && Search_transition(first_place_node,tran_search,var,op_return,num)){
	
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
	
	if(var->operator_out->output_value && Search_transition(first_place_node,tran_search,var->operator_out->output_value,op_return,num)){
		node_list[i++]->opnode = var->operator_out;
		var = var->operator_out->output_value;
	}
	else iterationflag=false;
	
	}
	if(!iterationflag && var->equal_op_out && Search_transition(first_place_node,tran_search,var,op_return,num)){
		
		if(nextflag)
			node_list[i++]->varnode = var;
		
		iterationflag=true;
		nextflag=false;
		
		if(var->equal_op_out->lhs_value && Search_transition(first_place_node,tran_search,var->equal_op_out->lhs_value,op_return,num)) {
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
	if(!iterationflag && var->dfgnode_out && Search_transition(first_place_node,tran_search,var,op_return,num)){
		
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
			if(var->dfgnode_out->output && Search_transition(first_place_node,tran_search,var->dfgnode_out->output,op_return,num)){
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
			if(Search_transition(var->place_ptr,tran_search,tran->output_var,op_return,num))
				{
				if(nextflag) node_list[i++]->varnode = var;
				node_list[i++]->trannode = tran; 
				store=true;break;}
				
			//else if(tran->output_var && Search_transition(first_place_node,tran_search,tran->output_var,op_return,num))
			//	{var = tran->output_var;break; }
				
		tran = tran->next_trans_node; 
		}
		nextflag=false;
		
		if(store && tran->output_var && Search_transition(tran->own_place_ptr, tran_search,tran->output_var,op_return,num))
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
	if(!iterationflag && var->transition_out && Search_transition(first_place_node,tran_search,var,op_return,num)){
	
		if(nextflag)
			node_list[i++]->varnode = var;
		
		iterationflag=true;
		nextflag=false;
		
		if(var->transition_out->output_var && Search_transition(var->transition_out->own_place_ptr, tran_search, var->transition_out->output_var,op_return,num)){
			 node_list[i++]->trannode = var->transition_out;
			 var = var->transition_out->output_var;
		}
		else iterationflag=false;
	}
	
	
}

number = i;
if(flag) delete_null_nodes(i); //for deleting the null nodes in the node_list

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

while(i<20 && node_list[i]){

	//if(!node_list[i]->opnode && !node_list[i]->varnode && !node_list[i]->placenode && !node_list[i]->trannode && !node_list[i]->equalnode && !node_list[i]->dfgnode){
		
		delete node_list[i];
		node_list[i]=NULL;
		//node_list[i] = node_list[i+1];
	//}
i++;
}


}


void Create_source_code(void){

ofstream myfile;
int i=0;


myfile.open("Csource.c");

if(myfile.is_open()){
	
	//the node_list always starts with the increment variable
	myfile << "#include <stdio.h>" << '\n' << "include <string.h>" << '\n' << "#include <stdlib.h>" << '\n';
	myfile << "void main(void){" << '\n' << "{" <<'\n';

while(node_list[i]){
	
	//if(node_list[i]->varnode){
		


}
	


}


}























