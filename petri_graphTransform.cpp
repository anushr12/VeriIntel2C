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
	Initialize_structures(cond_op, NULL,NULL,NULL,NULL);
	cond_op->equal_cond = new Equal_to_op;
	Initialize_structures(NULL, NULL,NULL,NULL,cond_op->equal_cond);
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
	Initialize_structures(NULL, NULL,NULL,NULL,cond_op->assign_expr);
	cond_op->assign_expr->lhs_value = new DeclareData ; //tempnode->expression_vt->left_value;
	assign_value(cond_op->assign_expr->lhs_value , tempnode->expression_vt->left_value);
	cond_op->assign_expr->rhs_value = new DeclareData ; //tempnode->expression_vt->right_value;
	assign_value(cond_op->assign_expr->rhs_value , tempnode->expression_vt->right_value);
	cond_op->assign_expr->opsymbol = '=';
	}
	else if(tempnode->expression_ct){
	cond_op->assign_expr = new Equal_to_op;
	Initialize_structures(NULL, NULL,NULL,NULL,cond_op->assign_expr);
	cond_op->assign_expr->lhs_value = new DeclareData ; //tempnode->expression_vt->left_value;
	assign_value(cond_op->assign_expr->lhs_value , tempnode->expression_ct->left_value);
	
	DeclareData *data = new DeclareData;
	Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,data,NULL, NULL,NULL);
	data->name = tempnode->expression_ct->const_expr;
	cond_op->assign_expr->rhs_value = data;
	cond_op->assign_expr->opsymbol = '=';
	}
	
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
	Initialize_structures(NULL, NULL,first_place_node,NULL,NULL);
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
	
	for(tmp = graph_first_node->always_node ; tmp!=NULL; tmp = tmp->next_n){
	
		place_node = new Place_block;
		Initialize_structures(NULL, NULL,place_node,NULL,NULL);
		
		if(tmp->event_controls){
			for( tnode = tmp->event_controls->first_port; tnode!=NULL ; tnode=tnode->next_n){
				
				if(Search_OutputVarFrom_Places( tnode , first_place_node, prev_tr , place_node ,NULL,prev_out )){
				
					//prev_tr->outgoing_external_place = place_node;
					//prev_tr->output_var->place_ptr = place_node;
					eventnotactive=false;
					continue;
				}
				else if( Search_var_InStateList(tnode , first_state))
				continue;
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
			
				attach_transition_nodes(place_node, false , tmp );
			
			else
				{delete place_node ; place_node = NULL;}

		}
		else{
			delete place_node ; place_node = NULL;}
	}

	
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
DeclareData *prev_outvar =NULL;
DFG_block *dfg_search = NULL;
Place_block *newplace=NULL;
Transition_block *prevtr = NULL; 

//dnode1 is from modinstantiation node
//dnode2 is from gnode which is the main FU node


for(tmpmod = mod_node , gnode=graph_first_node->next_node; tmpmod!=NULL , gnode!=NULL ; tmpmod = tmpmod_nextm, gnode=gnode->next_node){

		if(!strcmp(tmpmod->mod_name , gnode->name)){
			
			for(dnode1=tmpmod->ports_list->first_port , dnode2=gnode->operation_node->input_list->first_port; dnode1->next_n!=NULL; dnode1=dnode1->next_n , dnode2=dnode2->next_n){
				
				if(Attach_AssignNode_toDFG(dnode1)){
					if( (dnode2->data_type!=integer) && Search_OutputVarFrom_Places( dnode1 , first_place_node , prevtr ,  newplace/*null*/ , dfg_search , prev_outvar))
						{nodeready = true; dnode2->name=dnode1->name;}
						else if(dnode2->data_type==integer && !dnode1->next_n->next_n){
							 nodeready=true; dnode2->next_n->name = dnode1->name;
							// insert_in_list(tmpmod->ports_list, dnode2);
						}
					else { nodeready =false; break;}
				
				}
			}
					
			if(nodeready){
				DFG_block *dfg_node = new DFG_block;
				Initialize_structures(NULL, dfg_node,NULL,NULL,NULL);
				Create_DFG_from_FU(gnode , dfg_node , plnode , tmpmod );
				//search=true;
			
				//delete the tmpmod node
				tmpmod_nextm = tmpmod->nextm;
				if(tmpmod==graph_first_node->module_inst_node) graph_first_node->module_inst_node=tmpmod->nextm;
				else{
					tmpmod->prevm->nextm = tmpmod->nextm;
					tmpmod->nextm->prevm = tmpmod->prevm;
				}
				delete_ports_list(tmpmod->ports_list);
				delete tmpmod; tmpmod=NULL;
			}	
			else tmpmod_nextm = tmpmod->nextm;
			
			
		}
		else tmpmod_nextm = tmpmod->nextm;
	
}
//}// if the node matches with the node to be searched
		//else search=false;
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
					placenode->first_place_input = new DeclareData;
					Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,placenode->first_place_input,NULL,NULL,NULL);
					assign_value(placenode->first_place_input , cnode);
				}
				else{
					in_node = new DeclareData;
					Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,in_node,NULL,NULL,NULL);
					assign_value(in_node , cnode);
					Insert_placeInput_list(placenode , in_node);
				}
			}
		}
	}
	else{
	
		placenode->next_trans_node = true;
		Insert_in_transition_list(&transnode , placenode);
	}
	
	
	
			
}

}




// function to create different kinds of DFG's in a transition block irrespective of it is in nullalways list or not

void Create_node_in_Transition_block( Transition_block **CurrentTransNode  , Always_block *temp){


if(temp->CaseBlock)
{
	(*CurrentTransNode)->data_node = new DFG_block;
	Initialize_structures(NULL, (*CurrentTransNode)->data_node,NULL,NULL,NULL);
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
	Initialize_structures(NULL, (*CurrentTransNode)->data_node,NULL,NULL,NULL);
	(*CurrentTransNode)->output_var = new DeclareData;
	Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL, (*CurrentTransNode)->output_var,NULL,NULL,NULL);
	Create_DFG_from_assignexpr( (*CurrentTransNode)->data_node , temp->assign_expr , (*CurrentTransNode)->output_var);
	//break;
	//transnode->output_var = 


}


else if(temp->operate_expr)

{
	(*CurrentTransNode)->data_node = new DFG_block;
	Initialize_structures(NULL, (*CurrentTransNode)->data_node,NULL,NULL,NULL);
	(*CurrentTransNode)->output_var = new DeclareData;
	Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL, (*CurrentTransNode)->output_var,NULL,NULL,NULL);
	if( temp->operate_expr && !temp->comp_expr)
		Create_DFG_from_operateexpr( (*CurrentTransNode)->data_node , temp->operate_expr , (*CurrentTransNode)->output_var);
		//Create_DFG_from_operateexpr();
	else if(temp->comp_expr)
		Create_DFG_from_complexexpr( (*CurrentTransNode)->data_node, temp , (*CurrentTransNode)->output_var);
		
	

}

else if(temp->CondBlock)

	// to create the condition block function
{
	(*CurrentTransNode)->data_node = new DFG_block;
	(*CurrentTransNode)->output_var = new DeclareData;
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
	Initialize_structures(NULL, NULL,NULL,operate_n,NULL);
	dfg_node->operation_graph = operate_n;


	for( dnode1=gnode->operation_node->input_list->first_port ; dnode1!=NULL; dnode1=dnode1->next_n){
	
		prevtr=NULL;prev_outvar=NULL;
		if(dnode1->data_type!=integer && Search_OutputVarFrom_Places( dnode1 , first_place_node , prevtr ,  newplace/*null*/ , dfg_search , prev_outvar)){
	
	
				if(prevtr){
				prevtr->outgoing_external_dfg = dfg_node;
				prevtr->output_var->operator_out = operate_n;
				if(dnode1== gnode->operation_node->input_list->first_port)
					operate_n->op1 = prevtr->output_var;
				else operate_n->op2= prevtr->output_var;
				
				}
				else if( prev_outvar){
				prev_outvar->operator_out = operate_n;
				prev_outvar->dfgnode_out = dfg_node;
				if(dnode1== gnode->operation_node->input_list->first_port)
					operate_n->op1 = prev_outvar;
				else	operate_n->op2 = prev_outvar;
				}
		}
		else if(dnode1->data_type==integer){
			if(dnode1== gnode->operation_node->input_list->first_port){
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
	
	for(dnode2=modnode->ports_list->first_port;dnode2->next_n!=NULL; dnode2=dnode2->next_n);
	
		gnode->operation_node->output->name = dnode2->name ; 
		operate_n->output_value = new DeclareData;
		Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,operate_n->output_value,NULL,NULL,NULL);
		operate_n->output_value->name = gnode->operation_node->output->name;
		dfg_node->output = operate_n->output_value;
	
	
	
	
	// if the graph node contains another  operation as well
	//to be done later
	
}


}


//function to insert the assign expressions in this petri graph

bool Attach_AssignNode_toDFG( DeclareData *varsearch ){

Operate_op *operate_assign=NULL;
Assign_var *tmpassign=NULL ;
Assign_var *tmpassign_next = NULL;
Assign_const *tmpconst = NULL;
Assign_const *tmpconst_next=NULL;
bool attachflag = false;
Operate_node *tmpoper = NULL;
Operate_op *operation_node=NULL;
Operate_op *operate1 =NULL;
Operate_op *operate2=NULL;
ComplexOp_node *tmpcomp=NULL;
Place_block *newplace=NULL; //no need here, just to pass as null argument
Transition_block *trnode = NULL;
DeclareData *prev_data =NULL;
DeclareData *tmp = NULL;


if(graph_first_node->varassign_node){
	for(tmpassign = graph_first_node->varassign_node ; tmpassign!=NULL ; tmpassign = tmpassign_next){

		trnode=NULL; prev_data=NULL;
		if( !strcmp(varsearch->name,tmpassign->left_value->name) && Search_OutputVarFrom_Places(tmpassign->right_value , first_place_node , trnode,newplace,NULL,prev_data)){
			
			Equal_to_op *assign_op = new Equal_to_op;
			Initialize_structures(NULL, NULL,NULL,NULL,assign_op);
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
			else{
			tmpassign->prev_n->next_n = tmpassign->next_n;
			tmpassign->next_n->prev_n = tmpassign->prev_n;
			}
			delete tmpassign;
			tmpassign=NULL;
			break;
		}
		else
		tmpassign_next = tmpassign->next_n; 
	}
}

if(!attachflag && graph_first_node->constassign_node){

	for(tmpconst = graph_first_node->constassign_node ; tmpconst!=NULL ; tmpconst = tmpconst_next){
		if( !strcmp(varsearch->name,tmpconst->left_value->name)){
			varsearch->name = tmpconst->const_expr;
			varsearch->data_type = integer;
			attachflag=true;
			tmpconst_next = tmpconst->next_n; 
			if(tmpconst == graph_first_node->constassign_node){
			graph_first_node->constassign_node = tmpconst_next;
			//tmpconst_next->prev_n=NULL;
			}
			else{
			tmpconst->prev_n->next_n = tmpconst->next_n;
			tmpconst->next_n->prev_n = tmpconst->prev_n;
			}
			delete tmpconst;
			tmpconst=NULL;
			break;
		}
		else tmpconst_next = tmpconst->next_n;
	}
}
			
if(!attachflag && graph_first_node->operation_node){

	for(tmpoper = graph_first_node->operation_node ; tmpoper!=NULL; tmpoper = tmpoper->next_op){
		operate_assign = new Operate_op;
		Initialize_structures(NULL, NULL,NULL,operate_assign,NULL);
	
	   if(!strcmp(varsearch->name , tmpoper->output->name)){
	   	
	
		for(tmp = tmpoper->input_list->first_port ; tmp!=NULL;tmp = tmp->next_n){
		 	
		 	trnode=NULL;prev_data=NULL;
			if( ((tmp->data_type!=integer) && Search_OutputVarFrom_Places(tmp , first_place_node , trnode , newplace, NULL , prev_data)) || Search_var_InStateList(tmp, first_state)){
				
				
				if(trnode){
					 trnode->output_var->operator_out = operate_assign; 
					 if(tmp == tmpoper->input_list->first_port)
						 operate_assign->op1 = trnode->output_var;
					else 
						 operate_assign->op2 = trnode->output_var;
				}
				else if(prev_data){
					prev_data->operator_out = operate_assign;
					
					if(tmp == tmpoper->input_list->first_port)
						operate_assign->op1 = prev_data;
					else 
						operate_assign->op2 = prev_data;
				}
				else if(tmp == tmpoper->input_list->first_port) //only for state variables
					{ operate_assign->op1 = new DeclareData; assign_value(operate_assign->op1 , tmp);}
				else { operate_assign->op2 = new DeclareData; assign_value(operate_assign->op2 , tmp);}
				
			attachflag = true;
			break;
			}
		  //}
		  else attachflag=false;
		}
		if(operate_assign && attachflag){	
			operate_assign->output_value = new DeclareData;
			Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,operate_assign->output_value,NULL,NULL,NULL);
			operate_assign->output_value->name = tmpoper->output->name;
			Select_from_operator_list(operate_assign, tmpoper->operator_type);
		}
		
	}
	else attachflag=false;
	if(!attachflag) {delete operate_assign; operate_assign=NULL;}
	
	}
}

if(!attachflag && graph_first_node->complexop_node){
	
	for(tmpcomp = graph_first_node->complexop_node;tmpcomp!=NULL; tmpcomp=tmpcomp->next_op){
		operation_node = new Operate_op;
		operate1 = new Operate_op;
		Initialize_structures(NULL, NULL,NULL,operate1,NULL);
		Initialize_structures(NULL, NULL,NULL,operation_node,NULL);
		attachflag=false;
	if(!strcmp(varsearch->name , tmpcomp->out_value->name)){
		for(tmp = tmpcomp->basic_op1->input_list->first_port ; tmp!=NULL;tmp = tmp->next_n){
		
			trnode=NULL;prev_data=NULL;
				if(((tmp->data_type!=integer) && Search_OutputVarFrom_Places(tmp , first_place_node , trnode , newplace, NULL , prev_data)) || Search_var_InStateList(tmp, first_state)){
				
					
					if(trnode){
					
						trnode->output_var->operator_out = operate1; 
					 	if(tmp == tmpcomp->basic_op1->input_list->first_port)
						 operate1->op1 = trnode->output_var;
						 else 
						 operate1->op2 = trnode->output_var;
					}
					else if(prev_data){
						prev_data->operator_out = operate1;
					
						if(tmp == tmpcomp->basic_op1->input_list->first_port)
							operate1->op1 = prev_data;
						else 
							operate1->op2 = prev_data;
					}
					
					else if(tmp == tmpcomp->basic_op1->input_list->first_port){ //only for state variables
						operate1->op1 = new DeclareData ; assign_value(operate1->op1, tmp);}
					else { operate1->op2 = new DeclareData ; assign_value(operate1->op2 , tmp);}
					
						
				attachflag=true;
				Select_from_operator_list(operate1, tmpcomp->basic_op1->operator_type);
				
				operation_node->op3 = operate1;
				}
				else if(tmp->data_type==integer){
					if(tmp == tmpcomp->basic_op1->input_list->first_port){
						operate1->op1 = new DeclareData ; assign_value(operate1->op1, tmp);}
					else { operate1->op2 = new DeclareData ; assign_value(operate1->op2 , tmp);}
				}
					
			
				else attachflag=false;
			//}
		}
		//operate1->output_value = new DeclareData;
		//assign_value(operate1->output_value , tmpcomp->basic_op1->output);
		if(tmpcomp->basic_op2){
		
		operate2=new Operate_op;
		Initialize_structures(NULL, NULL,NULL,operate2,NULL);
		
			for(tmp = tmpcomp->basic_op2->input_list->first_port ; tmp!=NULL;tmp = tmp->next_n){
			
				trnode=NULL;prev_data=NULL;
				if( ((tmp->data_type!=integer) && Search_OutputVarFrom_Places(tmp , first_place_node , trnode , newplace, NULL , prev_data)) || Search_var_InStateList(tmp, first_state)){
					
					if(trnode){
					
						trnode->output_var->operator_out = operate2; 
					 if(tmp == tmpcomp->basic_op2->input_list->first_port)
						 operate2->op1 = trnode->output_var;
					 else 
						 operate2->op2 = trnode->output_var;
					}
					else if(prev_data){
						prev_data->operator_out = operate2;
					
						if(tmp == tmpcomp->basic_op2->input_list->first_port)
							operate2->op1 = prev_data;
						else 
							operate2->op2 = prev_data;
					}
					else if(tmp == tmpcomp->basic_op2->input_list->first_port)
						{ operate2->op1 = new DeclareData; assign_value(operate2->op1 , tmp);}
					else { operate2->op2 = new DeclareData; assign_value(operate2->op2 , tmp);}
				attachflag=true;
				Select_from_operator_list(operate2, tmpcomp->basic_op2->operator_type);
				operation_node->op3 = operate2;
				}
				else if(tmp->data_type==integer){
					if(tmp == tmpcomp->basic_op1->input_list->first_port){
						operate1->op1 = new DeclareData ; assign_value(operate1->op1, tmp);}
					else { operate1->op2 = new DeclareData ; assign_value(operate1->op2 , tmp);}
				}
				
				else attachflag=false;
			//}
			}
			if(!attachflag) {delete operate2;operate2=NULL;}
		}
		
		else if(tmpcomp->basic_operand){
		
			trnode=NULL;prev_data=NULL;
			if(((tmpcomp->basic_operand->data_type!=integer) && Search_OutputVarFrom_Places(tmpcomp->basic_operand , first_place_node , trnode , newplace, NULL , prev_data)) || Search_var_InStateList(tmpcomp->basic_operand, first_state)){
				
				//DeclareData *opvar = new DeclareData;
				if(trnode)
					{operation_node->op1 = trnode->output_var; trnode->output_var->operator_out = operation_node;}
				else if(prev_data)
					{operation_node->op1 = prev_data;prev_data->operator_out = operation_node;}
					
				else {operation_node->op1 = new DeclareData; assign_value(operation_node->op1 , tmpcomp->basic_operand);}
				attachflag=true;
				Select_from_operator_list(operation_node, tmpcomp->operator_type);
			}
			else if(tmpcomp->basic_operand->data_type!=integer){
				operation_node->op1 = new DeclareData; assign_value(operation_node->op1 , tmpcomp->basic_operand);}
			
			else attachflag=false;
			
			
		}	
		
		if(operation_node && attachflag){
			operation_node->output_value = new DeclareData;
			Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,operation_node->output_value,NULL,NULL,NULL);
			operation_node->output_value->name=tmpcomp->out_value->name;
		}
		}	
		if(!attachflag) { delete operation_node ; operation_node=NULL; delete operate1; operate1=NULL;}
		
	}
}		
	

return attachflag;

}
	
	
//function to create DFG from ifthenelse conditional block of always block

void Create_DFG_from_ifthenelse( DFG_block *dfgnode , Ifthenelse_block *condexpr , DeclareData *outvarnode){

	Condition_block *condop = new Condition_block;
	Initialize_structures(condop , NULL,NULL,NULL,NULL);
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
}






//function to create DFG from complex operations of always block


void Create_DFG_from_complexexpr(DFG_block *flownode , Always_block *temp , DeclareData *output){

DeclareData *tnode = NULL;
Operate_node *tmp_basicop=NULL;
ComplexOp_node *tmp_compop = NULL;
Operate_op *nextop3 = NULL;
bool opassign = false;bool opdone = false;

if(temp->operate_expr){ // if the always block also contains a basic operation node
	for(tmp_basicop = temp->operate_expr ; tmp_basicop!=NULL; tmp_basicop = tmp_basicop->next_op)
	Create_DFG_from_operateexpr( flownode , temp->operate_expr , output);
	// expand the graph from this operation node to the complex op node
	//step 1: search for the output_var of this basic opnode is in complex_op->basicop1 or basicop2
	//step 2: create another Operate_op node and then output_var->operator_out = Operate_op node
	for(tmp_compop = temp->comp_expr ; tmp_compop!=NULL; tmp_compop = tmp_compop->next_op){
	Operate_op *nextop1 = new Operate_op;
	Initialize_structures(NULL, NULL,NULL,nextop1,NULL);
	for( tnode = tmp_compop->basic_op1->input_list->first_port ; tnode!=NULL; tnode = tnode->next_n){
		
		if(flownode->operation_graph && !strcmp((flownode->operation_graph->output_value)->name,tnode->name)){
		flownode->operation_graph->output_value->operator_out = nextop1;
		 nextop1->op1 = flownode->operation_graph->output_value ;
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
	Initialize_structures(NULL, NULL,NULL,nextop2,NULL);
	
	opassign = false; opdone = false;
	for( tnode = tmp_compop->basic_op2->input_list->first_port ; tnode!=NULL; tnode = tnode->next_n){
	if(!tmp_compop->next_op && !tmp_compop->prev_op){
		if( flownode->operation_graph && !strcmp(flownode->operation_graph->output_value->name , tnode->name)){
	 	flownode->operation_graph->output_value->operator_out = nextop2;
	 	nextop2->op1 = flownode->operation_graph->output_value;
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
	 Initialize_structures(NULL, NULL,NULL,nextop3,NULL);
	
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
	Initialize_structures(NULL, NULL,NULL,tmp_op,NULL);
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
	Initialize_structures(NULL, NULL,NULL,tmp_op1,NULL);
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
	Initialize_structures(NULL, NULL,NULL,final_op,NULL);
	
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

	



// function to create DFG from operate nodes in always block

void Create_DFG_from_operateexpr( DFG_block *datanode , Operate_node *opnode , DeclareData *output){

DeclareData *tnode = NULL;

Operate_op *tempop = new Operate_op;
Initialize_structures(NULL, NULL,NULL,tempop,NULL);

for(tnode = opnode->input_list->first_port ; tnode!=NULL ; tnode = tnode->next_n){

	if(tnode == opnode->input_list->first_port){
		tempop->op1 = new DeclareData ; //tnode;
		assign_value(tempop->op1 , tnode);
	}
	else{
		
		tempop->op2 = new DeclareData ; //tnode;
		assign_value(tempop->op2 , tnode);
		break;
	}
	
}

assign_value(output , opnode->output);
tempop->output_value = output;  //opnode->output;
//assign_value(tempop->output_value , opnode->output);


//output = opnode->output;

//search for the operator type and put the op symbol appropriately
Select_from_operator_list(tempop ,  opnode->operator_type);

datanode->operation_graph = tempop;
}





// function to create dfg from assign_var node
void Create_DFG_from_assignexpr( DFG_block *dnode , Assign_var *expr, DeclareData *output){



Equal_to_op *equal_assign = new Equal_to_op;
Initialize_structures(NULL, NULL,NULL,NULL,equal_assign);

if(!expr->operation_rhs){
	//check this method otherwise allocate memory for lhs and rhs value
	equal_assign->lhs_value = new DeclareData; //expr->left_value;
	assign_value(equal_assign->lhs_value , expr->left_value);

	assign_value(output , expr->left_value); // the output is the output of this dfg
	equal_assign->rhs_value = output; //expr->right_value;
	//assign_value(equal_assign->rhs_value, expr->right_value);

	equal_assign->opsymbol = '=';
	
	//output = expr->left_value; // assign the output_var of the transition node
	
	dnode->assignment_graph = equal_assign;
}

else{
	
	Create_DFG_from_operateexpr( dnode , expr->operation_rhs , output);
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
		//node = temp_always;
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

}

}
	



void delete_null_always_list( Always_block *first_null_always_node){

Always_block *tmp_d = NULL;
Always_block *tmp_next = NULL;

for(tmp_d = first_null_always_node ; tmp_d ; tmp_d = tmp_next){
	
	tmp_next = tmp_d->next_n;
	
	if(tmp_d->assign_expr)
		{}
	else if(tmp_d->CaseBlock)
		{}
	else if(tmp_d->CondBlock)
		{}
	else if(tmp_d->operate_expr)
		{}
	else if(tmp_d->comp_expr)
		{}

	delete tmp_d;
	}

}



void Initialize_structures( Condition_block *node1 , DFG_block *node2 , Place_block *node3,Operate_op *node4 ,Equal_to_op *node5){

	if(node1){
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
		node4->output_value=NULL;
	}
	else if(node5){
		node5->lhs_value=NULL;
		node5->rhs_value=NULL;
	}
	
}


void delete_ports_list(PortList *list){

DeclareData *tmpn=NULL;
DeclareData *tmp_next=NULL;

for(tmpn = list->first_port; tmpn!=NULL;tmpn = tmp_next){
	
	tmp_next = tmpn->next_n;
	delete tmpn; tmpn=NULL;


}	

}








