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

// algorithm

// step 1: search for the always node whose event controls is NULL
//step 2: create the place and transition nodes for these always nodes

Place_block *first_place_node;
Always_block *first_null_always_node;



int create_petri_graph(Graph_node *graph_first_node , State_var *first_state){


// the first node is the datapath graph node which is to be used


  search_for_always_node(graph_first_node , true, false);
  

  Create_node_items(graph_first_node , first_state);
  
  //next create the nodes for the combinational assignments n then create nodes for the modules and attach them to the graph

return 1;


}



void Insert_in_transition_list( Transition_block **trnode , Place_block *place){

Transition_block *tmp = NULL;
// this function assumes the place node has multiple transition nodes


	//if(!first_place_node->first_trans_node)
	//first_place_node->first_trans_node = *trnode;


	for(tmp = place->first_trans_node ; tmp->next_trans_node!=NULL; tmp = tmp->next_trans_node);
	tmp->next_trans_node = *trnode;
	(*trnode)->prev_trans_node = tmp;
	(*trnode)->next_trans_node = NULL;
	


	// put the condition when transition is to be inserted into a different place node
	

}

//to insert continuous case statement expressions in continuous condition blocks inside one DFG node
void insert_in_condition_list( Condition_block *condop , DFG_block *node){

Condition_block *temp = NULL;
if(!node->condition_op)
node->condition_op = condop;

else{
for(temp = node->condition_op; temp->next_cond!= NULL; temp = temp->next_cond);
temp->next_cond = condop;
condop->prev_cond = temp;
condop->next_cond = NULL;
}

}




void Create_DFG_from_Caseblock( DFG_block *node, Case_Statement *case_expr , DeclareData *output){

Case_Statement *tempnode = NULL;
DeclareData *tmp_s = NULL;

//node->condition_op = new Condition_block;
Condition_block *cond_op = NULL;//new Condition_block;
//Initialize values

for(tempnode = case_expr ; tempnode != NULL; tempnode = tempnode->next_n){
	
	//the first case expr only contains the condition var and no other assign expr
	if(tempnode==case_expr){
		tmp_s = tempnode->condition_var;
		continue;
	}
	//the last case expr is default case which is not needed in this graph so send the value of output_var
	else if(tempnode->next_n == NULL){
		assign_value(output , cond_op->assign_expr->lhs_value);
		continue;	
		}

	//create the condition node to convert the condition = case_value
	cond_op = new Condition_block;
	Initialize_structures(cond_op, NULL,NULL,NULL,NULL,NULL);
	cond_op->equal_cond = new Equal_to_op;
	Initialize_structures(NULL, NULL,NULL,NULL,cond_op->equal_cond,NULL);
	cond_op->equal_cond->opsymbol = '=';
	cond_op->equal_cond->lhs_value = new DeclareData ; //tempnode->condition_var;
	Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,cond_op->equal_cond->lhs_value, NULL,NULL,NULL);
	assign_value(cond_op->equal_cond->lhs_value , tmp_s);
	DeclareData *dnode = new DeclareData;
	Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,dnode , NULL,NULL,NULL);
	dnode->name = tempnode->case_value;
	cond_op->equal_cond->rhs_value = dnode;
	
	if(tempnode->expression_vt){
	cond_op->assign_expr = new Equal_to_op;
	Initialize_structures(NULL, NULL,NULL,NULL,cond_op->assign_expr,NULL);
	cond_op->assign_expr->lhs_value = new DeclareData ; //tempnode->expression_vt->left_value;
	assign_value(cond_op->assign_expr->lhs_value , tempnode->expression_vt->left_value);
	cond_op->assign_expr->rhs_value = new DeclareData ; //tempnode->expression_vt->right_value;
	assign_value(cond_op->assign_expr->rhs_value , tempnode->expression_vt->right_value);
	cond_op->assign_expr->opsymbol = '=';
	}
	else if(tempnode->expression_ct){
	cond_op->assign_expr = new Equal_to_op;
	Initialize_structures(NULL, NULL,NULL,NULL,cond_op->assign_expr,NULL);
	cond_op->assign_expr->lhs_value = new DeclareData ; //tempnode->expression_vt->left_value;
	assign_value(cond_op->assign_expr->lhs_value , tempnode->expression_ct->left_value);
	
	DeclareData *data = new DeclareData;
	Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,data,NULL, NULL,NULL);
	data->name = tempnode->expression_ct->const_expr;
	cond_op->assign_expr->rhs_value = data;
	cond_op->assign_expr->opsymbol = '=';
	}
	
	cond_op->switchcase=true;
	insert_in_condition_list(cond_op,node);  //to this the list of the condition blocks are attached for a single caseblock of a single always node
	node->assignment_graph = NULL;
	//node->first_node = NULL;
	
	//if(tempnode->next_n == NULL)
		//assign_value(output , cond_op->assign_expr->lhs_value);
	
	}
	

}


// check for all event controls to the case block node and try to eliminate all the variables except the case select variable



void Create_node_items(Graph_node *graph_first_node , State_var *first_state){

Always_block *tmp = NULL;
Always_block *tmp_nextn=NULL;
bool flag = false;
bool eventnotactive = false;
DeclareData *tnode = NULL;
Transition_block *prev_tr = NULL;
Place_block *place_node =NULL;
//DFG_block *prev_dfg = NULL;
DeclareData *prev_out = NULL;

if(!first_place_node){

//use all the nodes in the null always list to attach to this place node
	first_place_node = new Place_block;
	Initialize_structures(NULL, NULL,first_place_node,NULL,NULL,NULL);
	first_place_node->token_active = true;
	attach_transition_nodes(NULL, true,NULL);
	Create_node_items(graph_first_node,first_state); // create the places now with event controls
	}
	
else{
	// only if all the inputs to a place are created before, only then the active token of this place will be active
	
	//traverse through all the always node from graph_start_node->always_node
	//in every always node->event_controls check if the variables are output_var of previous transition nodes
	//if all the output_var are available only then create the placenode
	// !eventnotactive means eventactive
	//prev_tr is sent NULL and 
	
	//delete_nullalways_list();
while(graph_first_node->always_node){
	for(tmp = graph_first_node->always_node ; tmp!=NULL; tmp = tmp_nextn){
	
		place_node = new Place_block;
		Initialize_structures(NULL, NULL,place_node,NULL,NULL,NULL);
		
		if(tmp->event_controls){
			for( tnode = tmp->event_controls->first_port; tnode!=NULL ; tnode=tnode->next_n){
				
				if(Search_OutputVarFrom_Places( tnode , first_place_node, prev_tr , place_node ,NULL,prev_out )){
				
					//prev_tr->outgoing_external_place = place_node;
					//prev_tr->output_var->place_ptr = place_node;
					eventnotactive=false;
					continue;
				}
				else if( Search_var_InStateList(tnode , first_state)) //search if the signal is in the state variable list
				continue;
				else if(tnode->data_type == input) // if the signal is an input variable RULE 2
					{eventnotactive=false;continue;}
				//search for the output var in the instantiated modules, and if yes then create DFG for the FU modules n attach the place
				else  {
					Search_varFrom_FU_Modules( tnode,graph_first_node->module_inst_node , place_node);
					if(Search_OutputVarFrom_Places( tnode , first_place_node, prev_tr , place_node ,NULL,prev_out )){
						//prev_tr->outgoing_external_place = place_node;
						//prev_tr->output_var->place_ptr = place_node;
						eventnotactive=false;
						continue;
					}		
				}
				
				
					eventnotactive = true;
					break;
				
			}
			if(!eventnotactive)
			//this means all the event controls of this always node are active and the place node can be created
			{
				attach_transition_nodes(place_node, false , tmp );
				tmp_nextn = tmp->next_n;
				if(tmp==graph_first_node->always_node) graph_first_node->always_node = tmp_nextn;
				else if(!tmp->next_n) tmp->prev_n->next_n=NULL;
				else{
					tmp->prev_n->next_n = tmp->next_n;
					tmp->next_n->prev_n = tmp->prev_n;
				}
				delete_null_always_list(tmp);
				//delete tmp ; tmp=NULL;
			}
				
			else
				{delete place_node ; 
				place_node = NULL;
				tmp_nextn = tmp->next_n;
				}

		}
		else{
			delete place_node ; place_node = NULL;
			tmp_nextn = tmp->next_n;
			if(tmp==graph_first_node->always_node) graph_first_node->always_node = tmp_nextn;
			else if(!tmp->next_n) tmp->prev_n->next_n = NULL;
			else{
				tmp->prev_n->next_n = tmp->next_n;
				tmp->next_n->prev_n = tmp->prev_n;
			}
			delete_null_always_list(tmp);
		}
	}
}

//check for the rest of the assign statements, operations and complex operations (combinational type)
while(graph_first_node->varassign_node || graph_first_node->operation_node || graph_first_node->complexop_node)
	Attach_AssignNode_toDFG(NULL,true);
	

}
}




//function to create the dfgs from FU modules only if both the inputs are already inserted in the graph created until this point

void Search_varFrom_FU_Modules( DeclareData *tnode , ModuleInstantiate *mod_node , Place_block *plnode){


ModuleInstantiate *tmpmod = NULL;
ModuleInstantiate *tmpmod_nextm=NULL;
DeclareData *node = NULL;
bool search = false;
bool nodeready=true;
Graph_node *gnode = NULL;
DeclareData *dnode1=NULL;
DeclareData *dnode2=NULL;
DeclareData *newdata=NULL;
DeclareData *prev_outvar =NULL;
DFG_block *dfg_search = NULL;
Place_block *newplace=NULL;
Transition_block *prevtr = NULL; 
State_var *statecheck=NULL;
//dnode1 is from modinstantiation node
//dnode2 is from gnode which is the main FU node


for(tmpmod = mod_node , gnode=graph_first_node->next_node; tmpmod!=NULL , gnode!=NULL ; tmpmod = tmpmod_nextm, gnode=gnode->next_node){

		if(!strcmp(tmpmod->mod_name , gnode->name)){
			
			for(dnode1=tmpmod->ports_list->first_port , dnode2=gnode->operation_node->input_list->first_port; dnode1->next_n!=NULL; dnode1=dnode1->next_n , dnode2=dnode2->next_n){
				
				Attach_AssignNode_toDFG(dnode1,false);
				
					 if(dnode1->data_type==integer){
						nodeready=true; dnode2->name = dnode1->name;}
					
					else if(dnode2->data_type==integer){
						newdata = new DeclareData;
						assign_value(newdata , dnode2);
						newdata->data_type=integer;
						newdata->next_n = dnode1->next_n;
						newdata->prev_n = dnode1;
						dnode1->next_n = newdata;
						nodeready=true;
					}
					else if(dnode1->data_type!=integer && Search_OutputVarFrom_Places( dnode1 , first_place_node , prevtr ,  newplace/*null*/ , dfg_search , prev_outvar)){
					//EDITING IN PROGRESS!!!!!!
					//check if both the input signals are in the same state
					if(dnode1->prev_n){
						
						if(prevtr) newplace = Search_place_of_input(prevtr->output_var);
						else if(prev_outvar) newplace = Search_place_of_input(prev_outvar);
						
						if(newplace){
							statecheck =  Search_state_in_PlaceInput(placecheck);
							if(statecheck && Check_state_of_input(statecheck,dnode1))
							
								{nodeready=true; dnode2->name = dnode1->name;}
						}
						else {
						//check in the 
						}
					}
					else {nodeready=true; dnode2->name = dnode1->name;}
					}
					
					
					else {nodeready = false ; break;}	
				
				
				
			}
		
					
			if(nodeready){
				DFG_block *dfg_node = new DFG_block;
				Initialize_structures(NULL, dfg_node,NULL,NULL,NULL,NULL);
				Create_DFG_from_FU(gnode , dfg_node , plnode , tmpmod );
				// search to connect the output var with the clock transition nodes
				Search_outputvar_from_ClockTransition(dfg_node);
			
				//delete the tmpmod node
				tmpmod_nextm = tmpmod->nextm;
				if(tmpmod==graph_first_node->module_inst_node) graph_first_node->module_inst_node=tmpmod->nextm;
				else if(!tmpmod->nextm) tmpmod->prevm->nextm=NULL;
				else{
					tmpmod->prevm->nextm = tmpmod->nextm;
					tmpmod->nextm->prevm = tmpmod->prevm;
				}
				delete_ports_list(tmpmod->ports_list);
				if(tmpmod->mod_name) {delete tmpmod->mod_name; tmpmod->mod_name = '\0';}
				delete tmpmod; tmpmod=NULL;
			}	
			else tmpmod_nextm = tmpmod->nextm;
			
			
		}
		else tmpmod_nextm = tmpmod->nextm;

//delete the datanode of this gnode
delete_data_list(gnode);
	
}
//}// if the node matches with the node to be searched
		//else search=false;
}
	
//function to search previous input's place	
Place_block *Search_place_of_input(DeclareData *input){

Transition_block *trannode=NULL;

trannode = first_place_node->first_trans_node;

while(trannode){



}



}



	
	
	
	
	
				
//function to connect the output var of dfg's to the input variable of only "clocked" transition nodes
void Search_outputvar_from_ClockTransition(DFG_block *dfg_node){


Transition_block *tmp=NULL;
Operate_op *tmpop=NULL;

tmp= first_place_node->first_trans_node;

while(tmp){
	if(tmp->data_node->assignment_graph){
	
		if(!strcmp(dfg_node->output->name,tmp->data_node->assignment_graph->rhs_value->name)){
			dfg_node->output->transition_out = tmp;
			//if(!dfg_node->operation_graph->output_value->equal_op_out) 
				dfg_node->operation_graph->output_value->transition_out = tmp;
				break;
		}
	}
	else if(tmp->data_node->operation_graph){
		//if(tmp->data_node->operation_graph->op3){
		
			tmpop = tmp->data_node->operation_graph;
			if(!strcmp(dfg_node->output->name, tmpop->op1->name) || !strcmp(dfg_node->output->name,tmpop->op2->name))
				dfg_node->output->transition_out = tmp;
	break;
	}
	
	else if(tmp->data_node->condition_op){
		if(!strcmp(dfg_node->output->name , tmp->data_node->condition_op->assign_expr->rhs_value->name)){
			dfg_node->output->transition_out = tmp;
			//if(!dfg_node->operation_graph->output_value->equal_op_out)
				dfg_node->operation_graph->output_value->transition_out = tmp;
		break;
		}
	}

tmp = tmp->next_trans_node;
}
		


}




void attach_transition_nodes(Place_block *placenode, bool attach_nullalways , Always_block *node_al ){


Always_block *temp = NULL;
DeclareData *cnode =NULL;
DeclareData *in_node=NULL;
DeclareData *prev_out=NULL;
Transition_block *prev_tr=NULL;
Transition_block *transnode = NULL;

if(attach_nullalways){
	if(!placenode) 
	first_place_node->next_trans_node = true;
	first_place_node->first_place_input = NULL;
	for( temp = first_null_always_node ; temp!=NULL; temp = temp->next_n){
		
		transnode = new Transition_block;
		Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,transnode);
		// select cases for different types of always node
		Create_node_in_Transition_block(&transnode , temp);
		transnode->own_place_ptr = first_place_node;
		if(temp==first_null_always_node)
		first_place_node->first_trans_node = transnode;
		else
		Insert_in_transition_list(&transnode , first_place_node);
		}
		
		
}		

else{
	
	transnode = new Transition_block;
	Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,transnode);
	Create_node_in_Transition_block(&transnode , node_al);
	transnode->own_place_ptr = placenode;
	
	
	//check if the placenode is newly created or already is active
	if( !placenode->first_trans_node)
	{
		placenode->first_trans_node = transnode;
		placenode->token_active = true;
		placenode->next_trans_node = false;
		for(cnode = node_al->event_controls->first_port ; cnode!=NULL; cnode=cnode->next_n){
			prev_tr=NULL;prev_out=NULL;
			if(Search_OutputVarFrom_Places( cnode , first_place_node, prev_tr , placenode ,NULL,prev_out ) || Search_var_InStateList(cnode,first_state)){
				if(prev_tr){
					prev_tr->outgoing_external_place = placenode;
					prev_tr->output_var->place_ptr = placenode;
				}
				else if(prev_out){
					prev_out->place_ptr = placenode;
				}
				if(!placenode->first_place_input){
					if(prev_tr) placenode->first_place_input = prev_tr->output_var;
					else if(prev_out) placenode->first_place_input = prev_out;
					
				}
				else{

					if(prev_tr) Insert_placeInput_list(placenode , prev_tr->output_var);
					else if(prev_out) Insert_placeInput_list(placenode , prev_out);
				}
			}
		}
		
		//if(transnode->data_node->condition_op->switchcase)
			//Insert_datainput_in_placelist(transnode);
	}
	else{
	
		placenode->next_trans_node = true;
		Insert_in_transition_list(&transnode , placenode);
		//if(transnode->data_node->condition_op->switchcase)
			//Insert_datainput_in_placelist(transnode);
	}
	
	
	
			
}

}


void Insert_datainput_in_placelist(Transition_block *transnode,bool &flag){

Condition_block *tmp=NULL;
//DeclareData *tmpvar = transnode->own_place_ptr->first_place_input;
DeclareData *prev_out=NULL;
Transition_block *prev_tr=NULL;
Place_block *placenode=NULL;

tmp = transnode->data_node->condition_op;

while(tmp){

	if(tmp->assign_expr && Search_OutputVarFrom_Places( tmp->assign_expr->rhs_value, first_place_node, prev_tr , placenode ,NULL,prev_out )){
		
		if(prev_tr){
		 prev_tr->outgoing_external_place = transnode->own_place_ptr;
		 Insert_placeInput_list(transnode->own_place_ptr ,prev_tr->output_var);
		 }
		else if(prev_out) {
		 prev_out->place_ptr = transnode->own_place_ptr;
		 Insert_placeInput_list(transnode->own_place_ptr, prev_out);
		 }
		 flag = true;
		
	}
	else flag = false;
	
tmp = tmp->next_cond;

}

}





// function to create different kinds of DFG's in a transition block irrespective of it is in nullalways list or not

void Create_node_in_Transition_block( Transition_block **CurrentTransNode  , Always_block *temp){


if(temp->CaseBlock)
{
	(*CurrentTransNode)->data_node = new DFG_block;
	Initialize_structures(NULL, (*CurrentTransNode)->data_node,NULL,NULL,NULL,NULL);
	(*CurrentTransNode)->output_var = new DeclareData;
	Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL, (*CurrentTransNode)->output_var,NULL,NULL,NULL);
	Create_DFG_from_Caseblock( (*CurrentTransNode)->data_node, temp->CaseBlock , (*CurrentTransNode)->output_var);
	//take the lhs value of any condition_block->assign_expr as output_var
	
	
	//break;
	//if(temp->next_n)
	//Insert_into_transition_list( &CurrentTransNode
			
}	
	
else if(temp->assign_expr)
{
	(*CurrentTransNode)->data_node = new DFG_block;
	Initialize_structures(NULL, (*CurrentTransNode)->data_node,NULL,NULL,NULL,NULL);
	(*CurrentTransNode)->output_var = new DeclareData;
	Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL, (*CurrentTransNode)->output_var,NULL,NULL,NULL);
	Create_DFG_from_assignexpr( (*CurrentTransNode)->data_node , temp->assign_expr , (*CurrentTransNode)->output_var);
	//break;
	//transnode->output_var = 


}


else if(temp->operate_expr)

{
	(*CurrentTransNode)->data_node = new DFG_block;
	Initialize_structures(NULL, (*CurrentTransNode)->data_node,NULL,NULL,NULL,NULL);
	(*CurrentTransNode)->output_var = new DeclareData;
	Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL, (*CurrentTransNode)->output_var,NULL,NULL,NULL);
	if( temp->operate_expr && !temp->comp_expr)
		Create_DFG_from_operateexpr( (*CurrentTransNode)->data_node , temp->operate_expr , (*CurrentTransNode)->output_var,true);
		//Create_DFG_from_operateexpr();
	else if(temp->comp_expr)
		Create_DFG_from_complexexpr( (*CurrentTransNode)->data_node, temp , (*CurrentTransNode)->output_var);
		
	

}

else if(temp->CondBlock)

	// to create the condition block function
{
	(*CurrentTransNode)->data_node = new DFG_block;
	Initialize_structures(NULL, (*CurrentTransNode)->data_node,NULL,NULL,NULL,NULL);
	(*CurrentTransNode)->output_var = new DeclareData;
	Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL, (*CurrentTransNode)->output_var,NULL,NULL,NULL);
	Create_DFG_from_ifthenelse( (*CurrentTransNode)->data_node, temp->CondBlock , (*CurrentTransNode)->output_var);
	
	//transnode->output_var = 
	
}

}


//function to insert the input to a place in its input list

void Insert_placeInput_list( Place_block *place_active , DeclareData *dnode){

DeclareData *temp_n = NULL;

for(temp_n = place_active->first_place_input ; temp_n->next_n!=NULL; temp_n=temp_n->next_n);
temp_n->next_n = dnode;
dnode->prev_n = temp_n;
dnode->next_n=NULL;


}





//function to search if a variable is output_var from already created place nodes
// the outputvar of the prev dfg node(prev_out) is being passed for attaching the assign node or operate nodes
//tran_node is returned only when the output_var to be searched is from a transition node

bool Search_OutputVarFrom_Places( DeclareData *var , Place_block *place_n , Transition_block*& tran_node , Place_block*& new_place , DFG_block *dfg_node , DeclareData*& prev_out){

Transition_block *tmp_tr = NULL;
//bool flag = false;
bool search = false;
DeclareData *outvar= NULL;
Operate_op *opnext=NULL;
Operate_op *opnext_s=NULL;

if(place_n){
	if(place_n->next_trans_node){
	for( tmp_tr = place_n->first_trans_node ; tmp_tr!=NULL;tmp_tr = tmp_tr->next_trans_node){
		if(var->name == tmp_tr->output_var->name)
			{ if(tmp_tr->output_var->place_ptr && new_place)
				{delete new_place; new_place=NULL; new_place = tmp_tr->output_var->place_ptr;}
			
			search = true;
			tran_node = tmp_tr;
			break;
			}
		else if(tmp_tr->outgoing_external_place && Search_OutputVarFrom_Places( var , tmp_tr->outgoing_external_place , tran_node ,new_place,dfg_node , prev_out)){
				search = true;
				//tran_node = tmp_tr;
				break;
				
		}
		else if(tmp_tr->outgoing_external_dfg && Search_OutputVarFrom_Places( var ,NULL, tran_node , new_place , tmp_tr->outgoing_external_dfg , prev_out)){
				//tran_node = tmp_tr;
				search = true;
				break;
			
		}
		//else{ 
			outvar = tmp_tr->output_var ;
			while(outvar->equal_op_out){
				if(!strcmp(var->name ,outvar->equal_op_out->lhs_value->name)){
					search = true;
					prev_out = outvar->equal_op_out->lhs_value;
					break;
				}
				else if(outvar->equal_op_out->lhs_value->place_ptr && Search_OutputVarFrom_Places(var , outvar->equal_op_out->lhs_value->place_ptr, tran_node,new_place,dfg_node,prev_out)){
						search = true;
						//tran_node = tmp_tr;
						break;
					
				}
				else if(outvar->equal_op_out->lhs_value->dfgnode_out && Search_OutputVarFrom_Places( var ,NULL, tran_node , new_place , outvar->equal_op_out->lhs_value->dfgnode_out , prev_out)){
						search = true;
						//tran_node = tmp_tr;
						break;
					
				}
				
			outvar = outvar->equal_op_out->lhs_value; //end of while loop
			}
		//}
		 if(!search){
			outvar = tmp_tr->output_var;
			while(outvar->operator_out && outvar->operator_out->output_value){
				if(!strcmp(var->name,outvar->operator_out->output_value->name)){
					search = true;
					prev_out = outvar->operator_out->output_value;
					break;
				}
				else if(outvar->operator_out->output_value->place_ptr && Search_OutputVarFrom_Places(var , outvar->operator_out->output_value->place_ptr, tran_node,new_place,dfg_node,prev_out)){
						search = true;
						//tran_node = tmp_tr;
						break;
					
				}
				else if(outvar->operator_out->output_value->dfgnode_out && Search_OutputVarFrom_Places( var ,NULL, tran_node , new_place ,outvar->operator_out->output_value->dfgnode_out, prev_out)){
						search = true;
						//tran_node = tmp_tr;
						break;
					
				}
			outvar = outvar->operator_out->output_value;
			}
		}
		if(!search){
			outvar = tmp_tr->output_var;
			opnext = outvar->operator_out;
			opnext_s = opnext;
			do{
			opnext = opnext_s;
			while(opnext){
				if(opnext->op3){
				opnext = opnext->op3;
				continue;
				}
				else if(opnext->output_value && !strcmp(var->name ,opnext->output_value->name)){
					search=true;
					prev_out = opnext->output_value;
					break;	
				}
					
				opnext = opnext->op3;
			}
			if(opnext_s) opnext_s = opnext_s->next_oper;
			}while(opnext_s);
		}
		
	}
}
else{

if(var->name == place_n->first_trans_node->output_var->name)
	{search = true;
	 tran_node = place_n->first_trans_node;
	}
else if( place_n->first_trans_node->outgoing_external_place && Search_OutputVarFrom_Places( var , place_n->first_trans_node->outgoing_external_place, tran_node , new_place,NULL,prev_out))
	search = true;
	//}
}

}
else if(dfg_node && dfg_node->output){
	if(dfg_node->output->name == var->name){
		search = true;
		prev_out = dfg_node->output;
		//break;
	}
	else if(dfg_node->output->equal_op_out){
		if(dfg_node->output->equal_op_out->lhs_value->name == var->name){
		search = true;
		prev_out = dfg_node->output->equal_op_out->lhs_value;
		//break;
		}
		else search = false;
		//else if(Search_OutputVarFrom_Places(var , NULL , tran_node , NULL , 

	}
}




return search;
}



//function to search if a variable is in the FSM state var list

bool Search_var_InStateList(DeclareData *node , State_var *first_state){

bool searchflag = false;
State_var *tmpn = NULL;

for(tmpn = first_state ; tmpn!=NULL;tmpn = tmpn->next_state){

	if(!strcmp(tmpn->state_name->name,node->name)){
	searchflag = true;break;
	}
	else continue;
}

return searchflag;
}



//function to create DFG from functional unit modules
void Create_DFG_from_FU( Graph_node *gnode , DFG_block *dfg_node , Place_block *plnode , ModuleInstantiate *modnode){

DeclareData *dnode1 =NULL;
DeclareData *dnode2 =NULL;
DeclareData *prev_outvar =NULL;
DFG_block *dfg_search = NULL;
Place_block *newplace=NULL;
Transition_block *prevtr = NULL; 
//previous transition node whose output var is one of the input variables to the FU
//dnode1 is the variable in the moduleInstantiate ports list
//dnode2 is the variable in the FU module node input ports list
// its needed to change the name of dnode2 to that of dnode1 in order to search for the variables in the previous place nodes

if(gnode->operation_node){
	Operate_op *operate_n = new Operate_op;
	Initialize_structures(NULL, NULL,NULL,operate_n,NULL,NULL);
	dfg_node->operation_graph = operate_n;


	for( dnode1=modnode->ports_list->first_port ; dnode1->next_n!=NULL; dnode1=dnode1->next_n){
	
		prevtr=NULL;prev_outvar=NULL;
		if(dnode1->data_type!=integer && Search_OutputVarFrom_Places( dnode1 , first_place_node , prevtr ,  newplace/*null*/ , dfg_search , prev_outvar)){
	
	
				if(prevtr){
				prevtr->outgoing_external_dfg = dfg_node;
				prevtr->output_var->operator_out = operate_n;
				if(dnode1== modnode->ports_list->first_port)
					operate_n->op1 = prevtr->output_var;
				else operate_n->op2= prevtr->output_var;
				
				}
				else if( prev_outvar){
				prev_outvar->operator_out = operate_n;
				prev_outvar->dfgnode_out = dfg_node;
				if(dnode1== modnode->ports_list->first_port)
					operate_n->op1 = prev_outvar;
				else	operate_n->op2 = prev_outvar;
				}
		}
		else if(dnode1->data_type==integer){
			if(dnode1== modnode->ports_list->first_port){
				operate_n->op1 = new DeclareData;
				Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL, operate_n->op1,NULL,NULL,NULL);
				operate_n->op1->name = dnode1->name;
			}
			else{
				operate_n->op2 = new DeclareData;
				Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL, operate_n->op2,NULL,NULL,NULL);
				operate_n->op2->name = dnode1->name;
			}
		}
	//}
		
	
	}
	
	Select_from_operator_list ( operate_n ,gnode->operation_node->operator_type);
	
	//for(dnode2=modnode->ports_list->first_port;dnode2->next_n!=NULL; dnode2=dnode2->next_n);
	if(dnode1->next_n==NULL){
		gnode->operation_node->output->name = dnode1->name ; 
		operate_n->output_value = new DeclareData;
		Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,operate_n->output_value,NULL,NULL,NULL);
		operate_n->output_value->name = gnode->operation_node->output->name;
		dfg_node->output = operate_n->output_value;
	}
	
	
	
	// if the graph node contains another  operation as well
	//to be done later
	
}


}


//bool Search_var_from_transitions(





//function to insert the assign expressions in this petri graph

void Attach_AssignNode_toDFG( DeclareData *varsearch,bool flag){

Operate_op *operate_assign=NULL;
Assign_var *tmpassign=NULL ;
Assign_var *tmpassign_next = NULL;
Assign_const *tmpconst = NULL;
Assign_const *tmpconst_next=NULL;
bool attachflag = false;
bool inputon=false;
Operate_node *tmpoper = NULL;
Operate_node *tmpoper_next=NULL;
Operate_op *operation_node=NULL;
Operate_op *operate1 =NULL;
Operate_op *operate2=NULL;
ComplexOp_node *tmpcomp=NULL;
ComplexOp_node *tmpcomp_next=NULL;
Place_block *newplace=NULL; //no need here, just to pass as null argument
Transition_block *trnode = NULL;
DeclareData *prev_data =NULL;
DeclareData *tmp = NULL;
State_var *statevar=NULL;

if(graph_first_node->varassign_node){
	for(tmpassign = graph_first_node->varassign_node ; tmpassign!=NULL ; tmpassign = tmpassign_next){

		trnode=NULL; prev_data=NULL;
		if( Search_OutputVarFrom_Places(tmpassign->right_value , first_place_node , trnode,newplace,NULL,prev_data)){
			
			Equal_to_op *assign_op = new Equal_to_op;
			Initialize_structures(NULL, NULL,NULL,NULL,assign_op,NULL);
			if(trnode)
				{trnode->output_var->equal_op_out = assign_op; assign_op->rhs_value = trnode->output_var;}
			else if(prev_data)
				{prev_data->equal_op_out = assign_op;assign_op->rhs_value = prev_data;}
			
			assign_op->lhs_value = new DeclareData;//tmpassign->left_value;
			Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,assign_op->lhs_value,NULL,NULL,NULL);
			assign_op->lhs_value->name = tmpassign->left_value->name;
			assign_op->opsymbol = '=';
			attachflag = true;
			tmpassign_next = tmpassign->next_n; 
			if(tmpassign == graph_first_node->varassign_node) graph_first_node->varassign_node = tmpassign_next;
			else if(!tmpassign->next_n) tmpassign->prev_n->next_n = NULL;
			else{
			tmpassign->prev_n->next_n = tmpassign->next_n;
			tmpassign->next_n->prev_n = tmpassign->prev_n;
			}
			delete tmpassign;
			tmpassign=NULL;
			//break;
		}
		else
		tmpassign_next = tmpassign->next_n; 
	}
}

if(graph_first_node->constassign_node){

	for(tmpconst = graph_first_node->constassign_node ; tmpconst!=NULL ; tmpconst = tmpconst_next){
		//if( !flag && SearchOutputVarFrom_Places(tmpconst->left_value, first_place_node , trnode,newplace,NULL,prev_data)){
			if(!flag && varsearch && !strcmp(varsearch->name , tmpconst->left_value->name)){
			varsearch->name = tmpconst->const_expr;
			varsearch->data_type = integer;
			attachflag=true;
			tmpconst_next = tmpconst->next_n; 
			if(tmpconst == graph_first_node->constassign_node)
			graph_first_node->constassign_node = tmpconst_next;
			else if(!tmpconst->next_n) tmpconst->prev_n->next_n=NULL;
			else{
			tmpconst->prev_n->next_n = tmpconst->next_n;
			tmpconst->next_n->prev_n = tmpconst->prev_n;
			}
			delete tmpconst;
			tmpconst=NULL;
			break;
			}
			else if(flag){
			attachflag=true;
			tmpconst_next = tmpconst->next_n; 
			if(tmpconst == graph_first_node->constassign_node)
			graph_first_node->constassign_node = tmpconst_next;
			else if(!tmpconst->next_n) tmpconst->prev_n->next_n=NULL;
			else{
			tmpconst->prev_n->next_n = tmpconst->next_n;
			tmpconst->next_n->prev_n = tmpconst->prev_n;
			}
			delete tmpconst;
			tmpconst=NULL;
			//break;
			}
			else
			 tmpconst_next = tmpconst->next_n;
	}
}
			
if(graph_first_node->operation_node){

	for(tmpoper = graph_first_node->operation_node ; tmpoper!=NULL; tmpoper = tmpoper_next){
		operate_assign = new Operate_op;
		Initialize_structures(NULL, NULL,NULL,operate_assign,NULL,NULL);
	
	 //  if(!strcmp(varsearch->name , tmpoper->output->name)){
	   	
	
		for(tmp = tmpoper->input_list->first_port ; tmp!=NULL;tmp = tmp->next_n){
		 	
		 	trnode=NULL;prev_data=NULL;
			if( ((tmp->data_type!=integer) && Search_OutputVarFrom_Places(tmp , first_place_node , trnode , newplace, NULL , prev_data)) || Search_var_InStateList(tmp, first_state )|| flag){
				
				inputon=true;
				continue;
		}
			else if(tmp->data_type==integer) inputon=true;
			else{
				inputon=false;
				break;
			}
		}
		for(tmp = tmpoper->input_list->first_port ; tmp!=NULL;tmp = tmp->next_n){
		 	
		 	trnode=NULL;prev_data=NULL;
			if( (inputon && (tmp->data_type!=integer) && Search_OutputVarFrom_Places(tmp , first_place_node , trnode , newplace, NULL , prev_data)) || (inputon && Search_var_InStateList(tmp, first_state))|| (inputon && flag)){
			
				if(trnode){
					if(!trnode->output_var->operator_out)
					 trnode->output_var->operator_out = operate_assign; 
					 else insert_in_operator_list( trnode->output_var , operate_assign);
					 
					 if(tmp == tmpoper->input_list->first_port)
						 operate_assign->op1 = trnode->output_var;
					else 
						 operate_assign->op2 = trnode->output_var;
				}
				else if(prev_data){
					if(!prev_data->operator_out)
					prev_data->operator_out = operate_assign;
					else insert_in_operator_list(prev_data , operate_assign);
					
					if(tmp == tmpoper->input_list->first_port)
						operate_assign->op1 = prev_data;
					else 
						operate_assign->op2 = prev_data;
				}
				
				else if(Search_var_from_statelist(tmp, statevar,false)){ //only for state variables
			
					operate_assign->op_state = statevar;
					statevar->op_out = operate_assign;
				}
				else if(tmp == tmpoper->input_list->first_port) //only for  variables which are not connected at the end after creation of entire petri net graph
					{ operate_assign->op1 = new DeclareData; assign_value( operate_assign->op1 ,tmp);
					 }//tmp->operator_out = operate_assign;}
				else { operate_assign->op2 = new DeclareData; assign_value(operate_assign->op2 ,tmp);
					}	// tmp->operator_out = operate_assign;}
				
			attachflag = true;
			//break;
			}
			else if(tmp->data_type==integer){
				if(tmp == tmpoper->input_list->first_port)
					{ operate_assign->op1 = new DeclareData; assign_value(operate_assign->op1 , tmp);operate_assign->op1->data_type=integer;}
				else {operate_assign->op2=new DeclareData; assign_value(operate_assign->op2 , tmp);operate_assign->op1->data_type=integer;}
				attachflag=true;
		  	}
		  else attachflag=false;
		}
		if(operate_assign && attachflag){	
			operate_assign->output_value = new DeclareData;
			Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,operate_assign->output_value,NULL,NULL,NULL);
			operate_assign->output_value->name = tmpoper->output->name;
			Select_from_operator_list(operate_assign, tmpoper->operator_type);
			delete tmpoper->output; tmpoper->output=NULL;
			delete_ports_list(tmpoper->input_list);
			tmpoper_next = tmpoper->next_op;
			if(tmpoper==graph_first_node->operation_node) graph_first_node->operation_node= tmpoper_next;
			else if(!tmpoper->next_op) tmpoper->prev_op->next_op = NULL;
			else{
				tmpoper->prev_op->next_op = tmpoper->next_op;
				tmpoper->next_op->prev_op = tmpoper->prev_op;
			}
			delete tmpoper; tmpoper=NULL;
		}
		
	//}
	else {attachflag=false; tmpoper_next = tmpoper->next_op;}
	if(!attachflag) {delete operate_assign; operate_assign=NULL;}
	
	}
}


if(graph_first_node->complexop_node){
	
	for(tmpcomp = graph_first_node->complexop_node;tmpcomp!=NULL; tmpcomp=tmpcomp_next){
		operation_node = new Operate_op;
		operate1 = new Operate_op;
		Initialize_structures(NULL, NULL,NULL,operate1,NULL,NULL);
		Initialize_structures(NULL, NULL,NULL,operation_node,NULL,NULL);
		//attachflag=false;
		inputon=false;
	//if(!strcmp(varsearch->name , tmpcomp->out_value->name)){
		for(tmp = tmpcomp->basic_op1->input_list->first_port ; tmp!=NULL;tmp = tmp->next_n){
		
			trnode=NULL;prev_data=NULL;
				if(((tmp->data_type!=integer) && Search_OutputVarFrom_Places(tmp , first_place_node , trnode , newplace, NULL , prev_data)) || Search_var_InStateList(tmp, first_state)){
				inputon=true;
				continue;
				}
				else if(tmp->data_type==integer) inputon=true;
				else { inputon = false;break;}
		}
		for(tmp = tmpcomp->basic_op1->input_list->first_port ; tmp!=NULL;tmp = tmp->next_n){
		
			trnode=NULL;prev_data=NULL;
				if((inputon && (tmp->data_type!=integer) && Search_OutputVarFrom_Places(tmp , first_place_node , trnode , newplace, NULL , prev_data)) || Search_var_InStateList(tmp, first_state)){
					
					if(trnode){
						if(!trnode->output_var->operator_out)
						trnode->output_var->operator_out = operate1;
						else insert_in_operator_list(trnode->output_var, operate1); 
					 	if(tmp == tmpcomp->basic_op1->input_list->first_port)
						 operate1->op1 = trnode->output_var;
						 else 
						 operate1->op2 = trnode->output_var;
					}
					else if(prev_data){
						if(!prev_data->operator_out)
						prev_data->operator_out = operate1;
						else insert_in_operator_list(prev_data, operate1);
						
						if(tmp == tmpcomp->basic_op1->input_list->first_port)
							operate1->op1 = prev_data;
						else 
							operate1->op2 = prev_data;
					}
					else if(Search_var_from_statelist(tmp, statevar,false)){ //only for state variables
					//if(tmp == tmpcomp->basic_op1->input_list->first_port) 
						operate1->op_state = statevar;
					//else  operate1->op2 = statevar; 
					statevar->op_out = operate1;
					}
					else if(tmp == tmpcomp->basic_op1->input_list->first_port){ //only for other variables
						operate1->op1 = new DeclareData ; assign_value(operate1->op1, tmp);}
					else { operate1->op2 = new DeclareData ; assign_value(operate1->op2 , tmp);}
					
						
				attachflag=true;
				Select_from_operator_list(operate1, tmpcomp->basic_op1->operator_type);
				}
				else if(tmp->data_type==integer){
					if(tmp == tmpcomp->basic_op1->input_list->first_port){
						operate1->op1 = new DeclareData ; assign_value(operate1->op1, tmp);operate1->op1->data_type=integer;}
					else { operate1->op2 = new DeclareData ; assign_value(operate1->op2 , tmp);operate1->op2->data_type=integer;}
				}
					
			
				else attachflag=false;
			//}
		} //for loop
		if(inputon){
			delete_ports_list(tmpcomp->basic_op1->input_list);
			delete tmpcomp->basic_op1; tmpcomp->basic_op1=NULL;
			operate1->op3 = operation_node;
			//operation_node->op3 = operate1;
		} 	
		
		
		inputon = false;
		if(tmpcomp->basic_op2){
		
		operate2=new Operate_op;
		Initialize_structures(NULL, NULL,NULL,operate2,NULL,NULL);
		//attachflag=false;
		
			for(tmp = tmpcomp->basic_op2->input_list->first_port ; tmp!=NULL;tmp = tmp->next_n){
			
				trnode=NULL;prev_data=NULL;
				if( ((tmp->data_type!=integer) && Search_OutputVarFrom_Places(tmp , first_place_node , trnode , newplace, NULL , prev_data)) || Search_var_InStateList(tmp, first_state)){
				
				inputon = true; 
				continue;
				}
				else if(tmp->data_type==integer) inputon=true;
				else{
					inputon = false ; break;
				}
			}
			for(tmp = tmpcomp->basic_op2->input_list->first_port ; tmp!=NULL;tmp = tmp->next_n){
			
				trnode=NULL;prev_data=NULL;
				if( (inputon && (tmp->data_type!=integer) && Search_OutputVarFrom_Places(tmp , first_place_node , trnode , newplace, NULL , prev_data)) || Search_var_InStateList(tmp, first_state)){
					
					if(trnode){
						if(!trnode->output_var->operator_out)
						trnode->output_var->operator_out = operate2;
						else insert_in_operator_list(trnode->output_var, operate2); 
						
					 if(tmp == tmpcomp->basic_op2->input_list->first_port)
						 operate2->op1 = trnode->output_var;
					 else 
						 operate2->op2 = trnode->output_var;
					}
					else if(prev_data){
						if(!prev_data->operator_out)
						prev_data->operator_out = operate2;
						else insert_in_operator_list(prev_data, operate2);
					
						if(tmp == tmpcomp->basic_op2->input_list->first_port)
							operate2->op1 = prev_data;
						else 
							operate2->op2 = prev_data;
					}
					else if(Search_var_from_statelist(tmp, statevar,false)){ //only for state variables
					//if(tmp == tmpcomp->basic_op2->input_list->first_port) 
						operate2->op_state = statevar;
					//else  operate2->op2 = statevar; 
					statevar->op_out = operate2;
					}
					
					else if(tmp == tmpcomp->basic_op2->input_list->first_port) //only for other variables
						{ operate2->op1 = new DeclareData; assign_value(operate2->op1 , tmp);}
					else { operate2->op2 = new DeclareData; assign_value(operate2->op2 , tmp);}
				attachflag=true;
				Select_from_operator_list(operate2, tmpcomp->basic_op2->operator_type);
				
				}
				else if(tmp->data_type==integer){
					if(tmp == tmpcomp->basic_op2->input_list->first_port){
						operate2->op1 = new DeclareData ; assign_value(operate2->op1, tmp);operate2->op1->data_type=integer;}
					else { operate2->op2 = new DeclareData ; assign_value(operate2->op2 , tmp);operate2->op2->data_type=integer;}
				}
				
				else attachflag=false;
			//}
			} //for loop
			if(!attachflag) {
				delete operate2;operate2=NULL;
			}
			if(inputon){
				delete_ports_list(tmpcomp->basic_op2->input_list);
				delete tmpcomp->basic_op2 ; tmpcomp->basic_op2=NULL;
				//operation_node->op3 = operate2;
				operate2->op3 = operation_node;
			} 
			
			//}
		}
		
		else if(tmpcomp->basic_operand){
		
			trnode=NULL;prev_data=NULL;
			if(((tmpcomp->basic_operand->data_type!=integer) && Search_OutputVarFrom_Places(tmpcomp->basic_operand , first_place_node , trnode , newplace, NULL , prev_data)) || Search_var_InStateList(tmpcomp->basic_operand, first_state)){
				
				//DeclareData *opvar = new DeclareData;
				if(trnode)
					{operation_node->op1 = trnode->output_var; 
					if(!trnode->output_var->operator_out)
					trnode->output_var->operator_out = operation_node;
					else insert_in_operator_list(trnode->output_var, operation_node);
					}
				else if(prev_data)
					{
					operation_node->op1 = prev_data;
					if(!prev_data->operator_out)
					prev_data->operator_out = operation_node;
					else insert_in_operator_list(prev_data, operation_node);
					}
					
				else if(Search_var_from_statelist(tmpcomp->basic_operand, statevar,false)){ //only for state variables
						operation_node->op_state = statevar;
					statevar->op_out = operation_node;
				}
					
				else {operation_node->op1 = new DeclareData; assign_value(operation_node->op1 , tmpcomp->basic_operand);}
				attachflag=true;
				Select_from_operator_list(operation_node, tmpcomp->operator_type);
			}
			else if(tmpcomp->basic_operand->data_type==integer){
				operation_node->op1 = new DeclareData; assign_value(operation_node->op1 , tmpcomp->basic_operand);}
				
			if(attachflag) {delete tmpcomp->basic_operand; tmpcomp->basic_operand=NULL;}
			
			else attachflag=false;
			
			
		}	
		
		if(operation_node && attachflag){
			operation_node->output_value = new DeclareData;
			Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,operation_node->output_value,NULL,NULL,NULL);
			operation_node->output_value->name=tmpcomp->out_value->name;
			delete tmpcomp->out_value; tmpcomp->out_value=NULL;
			tmpcomp_next = tmpcomp->next_op;
			if(tmpcomp==graph_first_node->complexop_node) graph_first_node->complexop_node = tmpcomp_next;
			else if(!tmpcomp->next_op) tmpcomp->prev_op->next_op = NULL;
			else{
				tmpcomp->prev_op->next_op = tmpcomp->next_op;
				tmpcomp->next_op->prev_op = tmpcomp->prev_op;
			}
			delete tmpcomp ; tmpcomp=NULL;
			
		}
		else tmpcomp_next = tmpcomp->next_op;
			
		if(!attachflag) { delete operation_node ; operation_node=NULL; delete operate1; operate1=NULL; tmpcomp_next = tmpcomp->next_op;}
		
	}
}		
	
//if(inputon || attachflag) attachflag=true;
//return attachflag;

}
	
	
//function to create DFG from ifthenelse conditional block of always block

void Create_DFG_from_ifthenelse( DFG_block *dfgnode , Ifthenelse_block *condexpr , DeclareData *outvarnode){

	Condition_block *condop = new Condition_block;
	Initialize_structures(condop , NULL,NULL,NULL,NULL,NULL);
	condop->if_cond_var = new DeclareData;
	assign_value(condop->if_cond_var , condexpr->if_condition_var);
	if(condexpr->then_expr_var){
		condop->assign_expr = new Equal_to_op;
		condop->assign_expr->lhs_value = new DeclareData;//condexpr->then_expr_var->left_value;
		assign_value(condop->assign_expr->lhs_value , condexpr->then_expr_var->left_value );
		condop->assign_expr->rhs_value = new DeclareData;//condexpr->then_expr_var->right_value;
		assign_value(condop->assign_expr->rhs_value , condexpr->then_expr_var->right_value ); 
		condop->assign_expr->opsymbol = '=';
	}
	else{
		condop->assign_expr = new Equal_to_op;
		condop->assign_expr->lhs_value = new DeclareData;//condexpr->then_expr_const->left_value;
		assign_value(condop->assign_expr->lhs_value , condexpr->then_expr_const->left_value);
		condop->assign_expr->rhs_value = new DeclareData;
		Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,condop->assign_expr->rhs_value  ,NULL,NULL,NULL);
		condop->assign_expr->rhs_value->name = condexpr->then_expr_const->const_expr;
		condop->assign_expr->opsymbol = '=';
	}
	
	dfgnode->condition_op = condop;
	assign_value(outvarnode , dfgnode->condition_op->assign_expr->lhs_value);
	dfgnode->output = outvarnode;
}






//function to create DFG from complex operations of always block


void Create_DFG_from_complexexpr(DFG_block *flownode , Always_block *temp , DeclareData *output){

DeclareData *tnode = NULL;
Operate_node *tmp_basicop=NULL;
Operate_op *prevop=NULL;
ComplexOp_node *tmp_compop = NULL;
Operate_op *nextop3 = NULL;
bool opassign = false;bool opdone = false;

if(temp->operate_expr){ // if the always block also contains a basic operation node
	for(tmp_basicop = temp->operate_expr ; tmp_basicop!=NULL; tmp_basicop = tmp_basicop->next_op)
		Create_DFG_from_operateexpr( flownode , temp->operate_expr , output,false);
	// expand the graph from this operation node to the complex op node
	//step 1: search for the output_var of this basic opnode is in complex_op->basicop1 or basicop2
	//step 2: create another Operate_op node and then output_var->operator_out = Operate_op node
	for(tmp_compop = temp->comp_expr ; tmp_compop!=NULL; tmp_compop = tmp_compop->next_op){
	Operate_op *nextop1 = new Operate_op;
	Initialize_structures(NULL, NULL,NULL,nextop1,NULL,NULL);
	for( tnode = tmp_compop->basic_op1->input_list->first_port ; tnode!=NULL; tnode = tnode->next_n){
		
		if(flownode->operation_graph && Search_var_from_prev_op(prevop , flownode->operation_graph ,tnode)/*!strcmp((flownode->operation_graph->output_value)->name,tnode->name)*/){
		prevop->output_value->operator_out = nextop1;
		 nextop1->op1 = prevop->output_value ;
		 opassign = true;
		}
		else if(!opassign){
		nextop1->op1 = new DeclareData;
		assign_value(nextop1->op1 , tnode);
		}
		if(tnode->next_n == NULL)
			opdone = true;
		if(opassign == true && opdone == true){
		nextop1->op2 = new DeclareData;
		assign_value(nextop1->op2 , tnode);
		}
		
		
	}
	nextop1->output_value = new DeclareData;
	Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,nextop1->output_value ,NULL,NULL,NULL);
	//assign_value(nextop1->output_value , temp->comp_expr->basic_op1->output);
	
	Operate_op *nextop2 = new Operate_op;
	Initialize_structures(NULL, NULL,NULL,nextop2,NULL,NULL);
	
	opassign = false; opdone = false;
	for( tnode = tmp_compop->basic_op2->input_list->first_port ; tnode!=NULL; tnode = tnode->next_n){
	if(!tmp_compop->next_op && !tmp_compop->prev_op){
		if( flownode->operation_graph && Search_var_from_prev_op(prevop , flownode->operation_graph , tnode)/*!strcmp(flownode->operation_graph->output_value->name , tnode->name)*/){
	 	prevop->output_value->operator_out = nextop2;
	 	nextop2->op1 = prevop->output_value;
	 	opassign = true;
	 	}
	 	}
	 /*else{
	 	if(!strcmp(nextop1->output_value->name , tnode->name)){
	 	nextop1->output_value->operator_out = nextop2;
	 	nextop2->op1 = nextop1->output_value;
	 	opassign = true;
	 	}
	 }*/
	 	
	 	if(opassign==false){
	 	nextop2->op1 = new DeclareData;
	 	assign_value(nextop2->op1 , tnode);
	 	}
	 	if(tnode->next_n == NULL)
	 	opdone = true;
	 	if(opassign == true && opdone == true){
	 	nextop2->op2 = new DeclareData;
	 	assign_value(nextop2->op2 , tnode);
	 	}
	 	
	 }
	 
	 //assign values to the outputs of the two basicops of the complex op node
	
	nextop2->output_value = new DeclareData;
	Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,nextop2->output_value ,NULL,NULL,NULL);
	
	//assign the operator type
	Select_from_operator_list(nextop1 , temp->comp_expr->basic_op1->operator_type);
	Select_from_operator_list(nextop2 , temp->comp_expr->basic_op2->operator_type);

	 // final operator
	 nextop3 = new Operate_op;
	 Initialize_structures(NULL, NULL,NULL,nextop3,NULL,NULL);
	
	 //nextop3->op3 = nextop1;
	// nextop3->op4 = nextop2;
	 nextop3->op1 = nextop1->output_value;
	 nextop1->output_value->operator_out = nextop3;
	 nextop3->op1->operator_in = nextop1;
	 
	 nextop3->op2 = nextop2->output_value;
	 nextop2->output_value->operator_out = nextop3;
	 nextop3->op2->operator_in = nextop2;
	
	 assign_value(output, temp->comp_expr->out_value);
	 nextop3->output_value = output;
	 
	 
	 //assign operator type
	 Select_from_operator_list(nextop3 , temp->comp_expr->operator_type);
	 
	 //output = nextop3->output_value;
	 } // end of FOR loop
	 
} 
	 
else if(!temp->operate_expr){
	//create flownode->operation_graph
	Operate_op *tmp_op = new Operate_op;
	Initialize_structures(NULL, NULL,NULL,tmp_op,NULL,NULL);
	for(tnode = temp->comp_expr->basic_op1->input_list->first_port; tnode!=NULL; tnode=tnode->next_n){
		if(tnode == temp->comp_expr->basic_op1->input_list->first_port){
		tmp_op->op1 = new DeclareData;
		assign_value(tmp_op->op1 , tnode);
		}
		else{
		tmp_op->op2 = new DeclareData;
		assign_value(tmp_op->op2 , tnode);
		}
	}
	
	tmp_op->output_value = new DeclareData;
	Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,tmp_op->output_value ,NULL,NULL,NULL);
	//assign_value(tmp_op->output_value , temp->comp_expr->basic_op1->output);
	//assign the operator types
	Select_from_operator_list(tmp_op , temp->comp_expr->basic_op1->operator_type);
	flownode->operation_graph = tmp_op;
	
	Operate_op *tmp_op1 = new Operate_op;
	Initialize_structures(NULL, NULL,NULL,tmp_op1,NULL,NULL);
	for(tnode = temp->comp_expr->basic_op2->input_list->first_port; tnode!=NULL; tnode=tnode->next_n){
		if(tnode == temp->comp_expr->basic_op2->input_list->first_port){
		tmp_op1->op1 = new DeclareData;
		assign_value(tmp_op1->op1 , tnode);
		}
		else{
		tmp_op1->op2 = new DeclareData;
		assign_value(tmp_op1->op2 , tnode);
		}
	}
	
	tmp_op1->output_value = new DeclareData;
	Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,tmp_op1->output_value ,NULL,NULL,NULL);
	//assign_value(tmp_op1->output_value , temp->comp_expr->basic_op2->output);
	
	//assign the operator type
	Select_from_operator_list(tmp_op1 , temp->comp_expr->basic_op2->operator_type);
	
	//create the final resultant complex op node
	Operate_op *final_op = new Operate_op;
	Initialize_structures(NULL, NULL,NULL,final_op,NULL,NULL);
	
	//attach the final op node to the previous basic op node
	tmp_op->output_value->operator_out = final_op;
	tmp_op1->output_value->operator_out = final_op;
	
	
	final_op->op1 = tmp_op->output_value;
	final_op->op1->operator_in = tmp_op;
	final_op->op2 = tmp_op1->output_value;
	final_op->op2->operator_in = tmp_op1;
	
	assign_value(output, temp->comp_expr->out_value); //assign the output of this dfg
	final_op->output_value = output;
	
	
	//assign the operator type
	Select_from_operator_list(final_op , temp->comp_expr->operator_type);
	
	//output = final_op->output_value;
	
	}
	
}

	
bool Search_var_from_prev_op( Operate_op*& prevop , Operate_op *opgraph , DeclareData *tnode){

bool flag=false;

while(opgraph){
	if(opgraph->output_value && !strcmp(tnode->name , opgraph->output_value->name)){
	
		flag = true;
		prevop = opgraph;
		break;
	}
	//else continue;

opgraph = opgraph->next_oper;
}

return flag;

}


// function to create DFG from operate nodes in always block

void Create_DFG_from_operateexpr( DFG_block *datanode , Operate_node *opnode , DeclareData *output,bool outputflag){

DeclareData *tnode = NULL;
Operate_op *prevop=NULL;
Operate_op *tmp=NULL;
Operate_node *tmpn=NULL;

Operate_op *tempop = NULL;
Initialize_structures(NULL, NULL,NULL,tempop,NULL,NULL);
tmpn = opnode;

while(tmpn){

	//if(opnode->prev_op)
	tempop = new Operate_op;
	Initialize_structures(NULL, NULL,NULL,tempop,NULL,NULL);
	for(tnode = tmpn->input_list->first_port ; tnode!=NULL ; tnode = tnode->next_n){
	
		if(tmpn->prev_op && Search_var_from_prev_op(prevop , datanode->operation_graph , tnode)){
		if(tnode == tmpn->input_list->first_port){
			tempop->op1 = prevop->output_value;
			prevop->output_value->operator_out = tempop;
		}
		else{
			
			tempop->op2 = prevop->output_value;
			prevop->output_value->operator_out = tempop;
			break;
		}
		}
		
		else{
			if(tnode == tmpn->input_list->first_port){
			tempop->op1 = new DeclareData ; //tnode;
			assign_value(tempop->op1 , tnode);
			}
			else{
			
			tempop->op2 = new DeclareData ; //tnode;
			assign_value(tempop->op2 , tnode);
			break;
			}
		}
				
	}
	

//search for the operator type and put the op symbol appropriately
	Select_from_operator_list(tempop ,  tmpn->operator_type);


	if(!tmpn->prev_op)
		datanode->operation_graph = tempop;
	else{
		
		for(tmp = datanode->operation_graph;tmp->next_oper!=NULL; tmp=tmp->next_oper);
		tmp->next_oper = tempop;
		tempop->next_oper=NULL;
		tempop->prev_oper = tmp;
	}

	//to give the output of the tempop
	if(outputflag){		
		assign_value(output , tmpn->output);
		tempop->output_value = new DeclareData;  //opnode->output;
		assign_value(tempop->output_value , tmpn->output);
	}
	else
	{ 	tempop->output_value = new DeclareData;
		assign_value(tempop->output_value , tmpn->output);
	}


tmpn = tmpn->next_op;
}

//while(opnode->next_op) opnode = opnode->next_op;




}





// function to create dfg from assign_var node
void Create_DFG_from_assignexpr( DFG_block *dnode , Assign_var *expr, DeclareData *output){



Equal_to_op *equal_assign = new Equal_to_op;
Initialize_structures(NULL, NULL,NULL,NULL,equal_assign,NULL);

if(!expr->operation_rhs){
	//check this method otherwise allocate memory for lhs and rhs value
	equal_assign->lhs_value = new DeclareData; //expr->left_value;
	assign_value(equal_assign->lhs_value , expr->left_value);

	assign_value(output , expr->left_value); // the output is the output of this dfg
	//equal_assign->rhs_value = output; //expr->right_value;
	equal_assign->rhs_value = new DeclareData; //expr->left_value;
	assign_value(equal_assign->rhs_value, expr->right_value);

	equal_assign->opsymbol = '=';
	
	//output = expr->left_value; // assign the output_var of the transition node
	
	dnode->assignment_graph = equal_assign;
	dnode->output = output;
}

else{
	
	Create_DFG_from_operateexpr( dnode , expr->operation_rhs , output,true);
}


}








void search_for_always_node(Graph_node *graph_start_node , bool search_first_node , bool search_node){

Graph_node *temp = NULL;
Always_block *temp_always = NULL;
Always_block *node = NULL;

// this is for searching the always node having null event controls only
if(search_first_node){

for(temp_always = graph_start_node->always_node ; temp_always !=NULL; temp_always = temp_always->next_n){

	if(temp_always->event_controls == NULL){
		// create the list for all the first always nodes
		node = new Always_block;
		Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,node,NULL,NULL,NULL,NULL);
		*node = *temp_always;
		insert_in_null_always_list(node);
		}
		
	else
	continue;
}

}

else{
}

}



void insert_in_operator_list( DeclareData *out, Operate_op *op_insert){

Operate_op *tmp=NULL;

for(tmp = out->operator_out ; tmp->next_oper!=NULL; tmp = tmp->next_oper);

tmp->next_oper  = op_insert;
op_insert->prev_oper = tmp;
op_insert->next_oper = NULL;

out->next_operator_out = true;
}








// to insert always nodes which dont have any event controls
void insert_in_null_always_list(Always_block *node){

Always_block *tmp = NULL;

if(!first_null_always_node){
	first_null_always_node = node;
	node->prev_n = NULL;
	node->next_n = NULL;
	}

else{
	for(tmp = first_null_always_node ; tmp->next_n!=NULL; tmp = tmp->next_n);
	tmp->next_n = node;
	node->prev_n = tmp;
	node->next_n = NULL;
    }
    
}
	
	
	
	
void Select_from_operator_list(Operate_op *tempop , unsigned operator_type){

switch(operator_type){

case VERI_REDAND:
{
	tempop->op_type = '&';
	break;
}
case VERI_REDOR:
{
	tempop->op_type = '|';
	break;
}
case VERI_REDNAND:
{
	tempop->op_type = '~&';
	break;
}
case VERI_REDXOR:
{
	tempop->op_type = '^';
	break;
}
case VERI_REDNOR:
{
	tempop->op_type = '~|';
	break;
}
case VERI_PLUS:
{
	tempop->op_type = '+';
	break;
}
case VERI_MIN:
{
	tempop->op_type = '-';
	break;
}
case VERI_MUL:

case VERI_AND:
{
	tempop->op_type = '*';
	break;
}
case VERI_DIV:
{
	tempop->op_type = '/';
	break;
}
case VERI_OR:
{
	tempop->op_type = '|';
	break;
}
case VERI_LT:
{
	tempop->op_type = '<';
	break;
}
case VERI_GT:
{
	tempop->op_type = '>';
	break;
}

}

}
	



void delete_null_always_list( Always_block *tmp_d){

//Always_block *tmp_d = NULL;
//Always_block *tmp_next = NULL;

//for(tmp_d = first_null_always_node ; tmp_d ; tmp_d = tmp_next){
	
//	tmp_next = tmp_d->next_n;
	
	if(tmp_d->assign_expr)
		{
			delete tmp_d->assign_expr; tmp_d->assign_expr=NULL;
		
		}
	else if(tmp_d->CaseBlock)
		{
			if(tmp_d->CaseBlock->expression_ct) {delete tmp_d->CaseBlock->expression_ct; tmp_d->CaseBlock->expression_ct=NULL;}
			if(tmp_d->CaseBlock->expression_vt) {delete tmp_d->CaseBlock->expression_vt; tmp_d->CaseBlock->expression_vt=NULL;}
			delete tmp_d->CaseBlock ; tmp_d->CaseBlock=NULL;
		}
	else if(tmp_d->CondBlock)
		{
			if(tmp_d->CondBlock->then_expr_const) {delete tmp_d->CondBlock->then_expr_const; tmp_d->CondBlock->then_expr_const=NULL;}
			if(tmp_d->CondBlock->then_expr_var) {delete tmp_d->CondBlock->then_expr_var; tmp_d->CondBlock->then_expr_var=NULL;}
			delete tmp_d->CondBlock;tmp_d->CondBlock=NULL;
		}
	else if(tmp_d->operate_expr)
		{
			delete_ports_list(tmp_d->operate_expr->input_list);
			delete tmp_d->operate_expr ; tmp_d->operate_expr=NULL;
		}
	else if(tmp_d->comp_expr)
		{
			if(tmp_d->comp_expr->basic_op1) {
				delete_ports_list(tmp_d->comp_expr->basic_op1->input_list);
				delete tmp_d->comp_expr->basic_op1; tmp_d->comp_expr->basic_op1=NULL;
			}
			if(tmp_d->comp_expr->basic_op2){
				delete_ports_list(tmp_d->comp_expr->basic_op2->input_list);
				delete tmp_d->comp_expr->basic_op2; tmp_d->comp_expr->basic_op2=NULL;
			}
			delete tmp_d->comp_expr ; tmp_d->comp_expr=NULL;
		}

	delete tmp_d;
	tmp_d=NULL;

}



void Initialize_structures( Condition_block *node1 , DFG_block *node2 , Place_block *node3,Operate_op *node4 ,Equal_to_op *node5,Path_node *node6){

	if(node1){
		node1->switchcase=false;
		node1->compare_cond=NULL;
		node1->if_cond_var=NULL;
		node1->equal_cond=NULL;
		node1->assign_expr=NULL;
		node1->next_cond=NULL;
		node1->prev_cond=NULL;
	}
	else if(node2){
		node2->output=NULL;
		node2->condition_op=NULL;
		node2->assignment_graph=NULL;
		node2->operation_graph=NULL;
	}
	else if(node3){
		node3->first_place_input=NULL;
		node3->first_trans_node=NULL;
		node3->token_active=false;
		node3->next_trans_node=false;
	}
	else if(node4){
		node4->op1=NULL;
		node4->op2=NULL;
		node4->op3=NULL;
		node4->op_state=NULL;
		node4->output_value=NULL;
		node4->next_oper=NULL;
		node4->prev_oper=NULL;
	}
	else if(node5){
		node5->lhs_value=NULL;
		node5->rhs_value=NULL;
	}
	else if(node6){
		node6->opnode=NULL;
		node6->varnode=NULL;
		node6->placenode=NULL;
		node6->trannode=NULL;
		node6->equalnode=NULL;
		node6->dfgnode=NULL;
	}
	
}


void delete_ports_list(PortList *list){

DeclareData *tmpn=NULL;
DeclareData *tmp_prev=NULL;
for(tmpn = list->first_port; tmpn->next_n!=NULL;tmpn = tmpn->next_n);
tmp_prev = tmpn;
while(tmp_prev){

	tmpn = tmp_prev;
	tmp_prev = tmpn->prev_n;
	delete tmpn; tmpn=NULL;

}

delete list ; list=NULL;	

}

void delete_data_list( Graph_node *gnode){

DeclareData *gnext=NULL;
DeclareData *gnext_prev=NULL;

for(gnext=gnode->data_node ; gnext->next_n!=NULL ; gnext = gnext->next_n);
gnext_prev = gnext;

while(gnext_prev){
	
	gnext = gnext_prev ; 
	gnext_prev = gnext->prev_n;
	delete gnext ; gnext=NULL;
	}
	
}







