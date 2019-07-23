

// NOTE : if node_list index no. is to be changed, change the line 1873, line 53, line 2006,  line 2056


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
#include "DFG_transform.h"
//#include "analysis_parse.cpp"

/////////////////////////////////////////aCHECKED RULE: 2 3 4 5 NOT DONE: 1 6 
/////////////////////////////////////////ERRORS: CRASHING IN SEARCH PLACE OF INPUT

using namespace std;

#ifdef VERIFIC_NAMESPACE
using namespace Verific ;
#endif

// algorithm

// step 1: search for the always node whose event controls is NULL
//step 2: create the place and transition nodes for these always nodes

Place_block *first_place_node;
Always_block *first_null_always_node;
Equal_to_op *first_EqualTo_node; //first equal to node
Place_block *first_parallel_place;
Path_node *node_list[10];
//const char *var_char[100]; //array to store the input variables which have not been attached in its current scope yet
DeclareData *varinput_list[100];
int list_num; //for varinput_list
//int char_num; //for var_char

int create_petri_graph(Graph_node *graph_first_node , State_var *first_state){

bool alwaysflag = true;
list_num = 0;
// the first node is the datapath graph node which is to be used
Initialize_array(varinput_list,100);
//Initialize_char(var_char,100);

  search_for_always_node(graph_first_node , true, false);
  
  Insert_operator_type(graph_first_node);

  Create_node_items(graph_first_node , first_state,alwaysflag);
  
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

//EDITING HERE
void Insert_operator_type(Graph_node *graph_first_node){

ModuleInstantiate *tmpmod = NULL;
Graph_node *gnode = NULL;

for(tmpmod = graph_first_node->module_inst_node , gnode = graph_first_node->next_node; tmpmod!=NULL,gnode!=NULL; tmpmod = tmpmod->nextm , gnode = gnode->next_node){
	if(!strcmp(tmpmod->mod_name,gnode->name)){
		Select_from_operator_list(NULL,tmpmod,gnode->operation_node->operator_type);
	}	
	
	
}


}


//function to search the var in the particular caseblock
//this fn doesnt check the condition_var
bool Search_var_in_CaseBlock(DeclareData *var, Case_Statement *caseblock){

bool search = false;

if(caseblock->expression_vt && !strcmp(var->name,caseblock->expression_vt->right_value->name))
	search = true;

return search;
}



//function to create DFG from the switchcase node
//prev_input indicates the variable which if present, only that particular case item is to be implemented(from parse tree)
void Create_DFG_from_Caseblock( DFG_block *node, Case_Statement *case_expr , DeclareData *output,Graph_node *graph_first_node,State_var *first_state,bool loopcheck,DeclareData *endvar,bool output_yes,DeclareData *prev_input){

Case_Statement *tempnode = NULL;
DeclareData *tmp_s = NULL , *prev_out = NULL;
Transition_block *prev_tr = NULL;
Place_block *place_node = NULL;
bool loop_create=  false;

//node->condition_op = new Condition_block;
Condition_block *cond_op = NULL;//new Condition_block;
//Initialize values

//if endvar exists, search the case_expr which has endvar and then only implement that

for(tempnode = case_expr ; tempnode != NULL; tempnode = tempnode->next_n){
	prev_tr = NULL;prev_out = NULL;
	
	//the first case expr only contains the condition var and no other assign expr
	if(tempnode==case_expr){
		tmp_s = tempnode->condition_var;
		continue;
	}
	//the last case expr is default case which is not needed in this graph so send the value of output_var
	else if(tempnode->next_n == NULL){
		if(!output_yes)
			assign_value(output , cond_op->assign_expr->lhs_value);
		
		continue;	
	}
	//CHANGED HERE
	if((endvar && !Search_var_in_CaseBlock(endvar,tempnode)) || (prev_input && !Search_var_in_CaseBlock(prev_input,tempnode)))
		continue;

	//create the condition node to convert the condition = case_value
	cond_op = new Condition_block;
	Initialize_structures(cond_op, NULL,NULL,NULL,NULL,NULL);
	cond_op->equal_cond = new Equal_to_op;
	Initialize_structures(NULL, NULL,NULL,NULL,cond_op->equal_cond,NULL);
	cond_op->equal_cond->opsymbol = '=';
	//search tmp_s(condition_var) from previous graph
	if(Search_OutputVarFrom_Places( tmp_s , first_place_node, prev_tr , place_node ,NULL,prev_out,graph_first_node,first_state,loopcheck,loop_create,true ) || Search_OutputVarFrom_Places(tmp_s,first_parallel_place,prev_tr,place_node,NULL,prev_out,graph_first_node,first_state,loopcheck,loop_create,true)){
		if(prev_out){
			//prev_out->dfgnode_out = node;
			cond_op->equal_cond->lhs_value = prev_out;
		}
		else if(prev_tr){
			//prev_tr->output_var->dfgnode_out = node;
			cond_op->equal_cond->lhs_value = prev_tr->output_var;
		}
		
	}
	
	else{
		prev_out=NULL;
		prev_tr=NULL;
		//varinput_list[list_num++] = tmp_s;		
	}
	
	DeclareData *dnode = new DeclareData;
	Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,dnode , NULL,NULL,NULL);
	dnode->name = tempnode->case_value;
	dnode->data_type = integer;
	cond_op->equal_cond->rhs_value = dnode;
	if(endvar){
		cond_op->equal_cond->lhs_value = new DeclareData;
		assign_value(cond_op->equal_cond->lhs_value, tmp_s);
	}
	
	if(tempnode->expression_vt){
		cond_op->assign_expr = new Equal_to_op;
		Initialize_structures(NULL, NULL,NULL,NULL,cond_op->assign_expr,NULL);
		prev_tr = NULL;prev_out = NULL;
		//check if the output of the expression already is created as a loop CHANGED HERE
		if(output_yes)
			cond_op->assign_expr->lhs_value = output;
		else if(Search_OutputVarFrom_Places( tempnode->expression_vt->left_value, first_place_node, prev_tr , place_node ,NULL,prev_out,graph_first_node,first_state,loopcheck,loop_create,true ) || Search_OutputVarFrom_Places(tempnode->expression_vt->left_value,first_parallel_place,prev_tr,place_node,NULL,prev_out,graph_first_node,first_state,loopcheck,loop_create,true)){
			if(prev_out)
				cond_op->assign_expr->lhs_value = prev_out;
			else if(prev_tr)
				cond_op->assign_expr->lhs_value = prev_tr->output_var;
		}
		else{
			if(!cond_op->prev_cond){
				cond_op->assign_expr->lhs_value = new DeclareData ; //tempnode->expression_vt->left_value;
				assign_value(cond_op->assign_expr->lhs_value , tempnode->expression_vt->left_value);
			}
			else{
				cond_op->assign_expr->lhs_value = cond_op->prev_cond->assign_expr->lhs_value;
			}
		}
		prev_tr = NULL;prev_out = NULL;
		//first search if the right value of each expression is available as output_var, if not create separate values
		if(Search_OutputVarFrom_Places( tempnode->expression_vt->right_value, first_place_node, prev_tr , place_node ,NULL,prev_out,graph_first_node,first_state,loopcheck,loop_create,true ) || Search_OutputVarFrom_Places(tempnode->expression_vt->right_value,first_parallel_place,prev_tr,place_node,NULL,prev_out,graph_first_node,first_state,loopcheck,loop_create,true)){
			if(prev_out){
				//CHANGED HERE NOW!
				//prev_out->dfgnode_out = node;
				//prev_out->equal_op_out = cond_op->assign_expr;
				cond_op->assign_expr->rhs_value= prev_out;
			}
			else if(prev_tr){
			//	prev_tr->output_var->dfgnode_out = node;
				//prev_tr->output_var->equal_op_out = cond_op->assign_expr;
				cond_op->assign_expr->rhs_value = prev_tr->output_var;
			}
			
		}
		else if(endvar && !strcmp(endvar->name , tempnode->expression_vt->right_value->name)){
			//if(!endvar->equal_op_out) endvar->equal_op_out = cond_op->assign_expr;
			//else Insert_in_equalto_list(NULL,endvar,cond_op->assign_expr);
			cond_op->assign_expr->rhs_value = endvar;
			//endvar->dfgnode_out = node;
		}
		else{
			cond_op->assign_expr->rhs_value = new DeclareData;
			assign_value(cond_op->assign_expr->rhs_value,tempnode->expression_vt->right_value);
			//cond_op->assign_expr->rhs_value->dfgnode_out = node;
			//insert the var in var_list if its not attached
			//varinput_list[list_num++] = cond_op->assign_expr->rhs_value;
		}
	
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
	data->data_type = integer;
	cond_op->assign_expr->rhs_value = data;
	cond_op->assign_expr->opsymbol = '=';
	}
	
	cond_op->switchcase=true;
	insert_in_condition_list(cond_op,node);  //to this the list of the condition blocks are attached for a single caseblock of a single always node
	node->assignment_graph = NULL;
	node->output = output; //dfgnode output is the same as transition output
	
	
	}
	

}

//function to search a variable as output of var assignment and assign operations
//RULE 4
bool Search_assign_list(DeclareData *searchvar,Graph_node *node,DeclareData*& assign_ret, Operate_node*& op_ret){

bool flag = false;
Assign_var *tmp=NULL , *tmp_n = NULL;
Operate_node *tmpop=NULL;
Ifthenelse_block *condnull=NULL;

//op_ret and assign_ret are null nodes for returning the search results from assign var list or assign op list

if(node->varassign_node){
	tmp = node->varassign_node;
	while(tmp){
		if(!strcmp(searchvar->name , tmp->left_value->name)){
			flag = true;
			assign_ret = tmp->right_value;
			//here only the right value is being sent, so assign node can be deleted
			delete_nodes(node,tmp,op_ret,condnull);
			break;
		}
		tmp = tmp->next_n;
	}
}
if(!flag && node->operation_node){
	tmpop = node->operation_node;
	while(tmpop){
		if(!strcmp(searchvar->name , tmpop->output->name)){
			flag=true;
			op_ret = tmpop;
			//delete_nodes(node,tmp_n,tmpop,condnull);
			break;
		}
		tmpop = tmpop->next_op;
	}

}


return flag;

}

//function transfers values from "copyfrom" to "copyto" and put control input vars in eventlist
//function also copies values from one operation node to the other
void Copy_block_to_node(Ifthenelse_block*& copyto, Ifthenelse_block *copyfrom, PortList *list , Operate_node*& operationto , Operate_node *operationfrom,bool insert){

DeclareData *node=NULL , *tmp = NULL, *tmp_new = NULL;

if(copyfrom && copyfrom->if_condition_var){
	copyto->if_condition_var = new DeclareData;
	assign_value(copyto->if_condition_var,copyfrom->if_condition_var);
	if(insert){
		node = new DeclareData;
		assign_value(node,copyfrom->if_condition_var);
		insert_in_list(list,node);
	}
}
if(copyfrom && copyfrom->then_expr_var){
	copyto->then_expr_var = new Assign_var;
	Initialize_values(NULL,NULL,NULL,copyto->then_expr_var,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
	copyto->then_expr_var->right_value = new DeclareData;
	assign_value(copyto->then_expr_var->right_value,copyfrom->then_expr_var->right_value);
	if(insert){
		node = new DeclareData;
		assign_value(node,copyfrom->then_expr_var->right_value);
		insert_in_list(list,node);
	}
	copyto->then_expr_var->left_value =new DeclareData;
	assign_value(copyto->then_expr_var->left_value,copyfrom->then_expr_var->left_value);
}
if(copyfrom && copyfrom->equal_condition){
	copyto->equal_condition = new Assign_const;
	Initialize_values(NULL,NULL,NULL,NULL,copyto->equal_condition,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
	copyto->equal_condition->left_value = new DeclareData;
	assign_value(copyto->equal_condition->left_value, copyfrom->equal_condition->left_value);
	copyto->equal_condition->const_expr = copyfrom->equal_condition->const_expr;

}
if(copyfrom && copyfrom->then_var){
	copyto->then_var = new DeclareData;
	assign_value(copyto->then_var,copyfrom->then_var);
}

if(operationfrom){
	operationto->input_list = new PortList;
	Initialize_values(NULL,operationto->input_list,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
	tmp = operationfrom->input_list->first_port;
	while(tmp){
		tmp_new = new DeclareData;
		assign_value(tmp_new,tmp);
		if(tmp == operationfrom->input_list->first_port)
			operationto->input_list->first_port = tmp_new ;
		else
			insert_in_list(operationto->input_list,tmp_new);
		tmp = tmp->next_n;
	}
	operationto->output = new DeclareData;
	assign_value(operationto->output,operationfrom->output);
	operationto->operator_type = operationfrom->operator_type;
	
}


}


//fn to modify the ports list according to always_block input variables
void Modify_ports_list(PortList*& control_list,Always_block *block){

DeclareData *tmp = NULL;
DeclareData *tmp_next = NULL;

tmp = control_list->first_port;

while(tmp){
	if(!strcmp(block->CondBlock->if_condition_var->name,tmp->name) || !strcmp(block->CondBlock->then_expr_var->right_value->name,tmp->name)){
		tmp = tmp->next_n;
		continue;
	}
	else if(block->CondBlock->equal_condition && !strcmp(block->CondBlock->equal_condition->left_value->name,tmp->name)){
		tmp = tmp->next_n;
		continue;
	}
	else{
		tmp_next = tmp->next_n;
		if(!tmp->next_n)
			tmp->prev_n->next_n = NULL;
		else if(tmp == control_list->first_port)
			control_list->first_port = tmp_next;
		else{
			tmp->prev_n->next_n = tmp->next_n;
			tmp->next_n->prev_n = tmp->prev_n;
		}
		Delete_var_node(tmp);
	}
	tmp = tmp_next;
}

}


//REFERENCE 1
// only if all the inputs to a place are created before, only then the active token of this place will be active
	
	//traverse through all the always node from graph_start_node->always_node
	//in every always node->event_controls check if the variables are output_var of previous transition nodes
	//if all the output_var are available only then create the placenode
	// !eventnotactive means eventactive
	//prev_tr is sent NULL and 
//REFERENCE 2
//  the if_condvar is the event control list. Search for the condvar in the assign nodes, 
		//take the inputvariables which generate this condvar, and then replace condvar by the inputvariables in the event_control list 
		
			// if the conditional node contains only then var, this generates only control signal	

//REFERENCE 3
//put the operate expr  in another always node with only an operation node
//since its an operate expr, assumed that it has only state signals, thus it generates only a control signal
//this operate expr, shall be added to the graph_node list of operation nodes
//put the operate expr in the list of only operation nodes without an always node, and delete this always node


// check for all event controls to the case block node and try to eliminate all the variables except the case select variable
void Create_node_items(Graph_node *graph_first_node , State_var *first_state,bool alwaysflag){

Always_block *tmp = NULL , *tmp_nextn=NULL , *always_temp=NULL , *tmp_position=NULL , *tmp_null = NULL;
bool flag = false , asyncnode=false, eventnotactive = true,opflag=true,opflag1=true,statelist_edited = false,loopcreate = false,loop_node = false,checkflag = true;
ModuleInstantiate *tmpnull = NULL;
DeclareData *tnode = NULL , *node=NULL , *node_next=NULL,*tmpsearch = NULL,*tmpinput=NULL,*tmpnode= NULL,*tmpdata = NULL,*condvar=NULL,*varassign=NULL,*prev_out = NULL;
Transition_block *prev_tr = NULL;
Place_block *place_node =NULL;
Compare_operator *compare_op = NULL;
Operate_node *operassign=NULL,*tmp_basic=NULL,*tmp_oper=NULL;
Ifthenelse_block *tmpexpr=NULL;
State_var *state_list[10],*ret_state=NULL;


if(alwaysflag && !first_place_node){

//use all the nodes in the null always list to attach to this place node
	first_place_node = new Place_block;
	Initialize_structures(NULL, NULL,first_place_node,NULL,NULL,NULL);
	first_place_node->token_active = true;
	attach_transition_nodes(NULL, true,NULL,graph_first_node,first_state,true,NULL,NULL,false,NULL);
	if(!graph_first_node->always_node) 
		alwaysflag = false;
	Create_node_items(graph_first_node,first_state,alwaysflag); // create the places now with event controls
}
	
else{
	//REFERENCE 1
	//delete_nullalways_list();
	//CHANGE THIS METHOD OF WHILE LOOP!!! EDITING HERE
while(checkflag && graph_first_node->always_node){
	
	for(tmp = graph_first_node->always_node ; tmp!=NULL; tmp = tmp_nextn){
	
		tmp_position=tmp; asyncnode = false;
		eventnotactive = true;loop_node = false;
		place_node = new Place_block;
		Initialize_structures(NULL, NULL,place_node,NULL,NULL,NULL);
		//RULE 4
		
		if(tmp->CondBlock){
		//REFERENCE 2
			if(tmp->CondBlock->then_var){
				tmpexpr = tmp->CondBlock;
				Create_and_attach_cond(tmpexpr,graph_first_node);
				//if the always node is generating a control signal, then this node becomes a wired conditional node as a part of the graphnode
				tmp_nextn = tmp->next_n;
				delete_ports_list(tmp->event_controls);
				Delete_always_node(graph_first_node,tmp,true,tmpexpr,tmpnull,true,tmp_oper);
				continue;
			}
	
			//this is for async reset always nodes
			else if(Search_assign_list(tmp->CondBlock->if_condition_var,graph_first_node,varassign,operassign)){
				if(varassign){
				//replace condvar with the rhs value of the assign node(varassign) and update the event_list
					Replace_ports_list(tmp,tmp->event_controls,varassign,true,NULL,graph_first_node);
				}
				else if(operassign)
					Replace_ports_list(tmp,tmp->event_controls,NULL,false,operassign,graph_first_node);
					
				asyncnode = true;
					
			}
			//this case for condblock with else expr
			else if(tmp->CondBlock->else_expr_block){
				tmpexpr = tmp->CondBlock->else_expr_block;
				while(tmpexpr){
					always_temp = new Always_block;
					Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,always_temp,NULL,NULL,NULL,NULL);
					always_temp->event_controls = new PortList;
					 Initialize_values(NULL, always_temp->event_controls,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
					always_temp->CondBlock = new Ifthenelse_block;
					 Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,always_temp->CondBlock,NULL,NULL,NULL,NULL,NULL);
					 Copy_block_to_node(always_temp->CondBlock,tmpexpr,always_temp->event_controls,tmp_oper,NULL,true);
					 Insert_between_alwayslist(tmp_position,always_temp,graph_first_node);
					 tmp_position=always_temp;
					 tmpexpr = tmpexpr->else_expr_block;
				}
				Modify_ports_list(tmp->event_controls,tmp);
				Delete_always_node(graph_first_node,tmp,true,tmp->CondBlock->else_expr_block,tmpnull,false,tmp_oper);
			}
			//this case for condblock without else expr
			else if(asyncnode){
				node = tmp->event_controls->first_port;
				while(node){
					if(strcmp(node->name,tmp->CondBlock->if_condition_var->name) || strcmp(node->name,tmp->CondBlock->then_expr_var->right_value->name)){
						node_next = node->next_n;
						if(!node->prev_n) tmp->event_controls->first_port = node->next_n;
						else if(!node->next_n) node->prev_n = NULL;
						else {
							node->prev_n->next_n = node->next_n;
							node->next_n->prev_n = node->prev_n;
						}
						delete node;
						node=NULL;
						
					}
					else node_next = node->next_n;
					node = node_next;
				}
				delete tmp->event_controls;
				tmp->event_controls=NULL;
			}
			
		}
		//RULE 5(modified) all the operation or comp oper expr nodes have been converted into conditional nodes in analysis_parse function, thus, if there are any operation nodes here, this means the nodes consists of only state signals
		 if(tmp && tmp->operate_expr){
			 	if(tmp->comp_expr) opflag = true;
			 	else if(tmp->operate_expr) opflag=false;
			 	if(tmp->CondBlock){
			 		tmpexpr = tmp->CondBlock;
			 		while(tmpexpr){
			 			if( !opflag && !strcmp(tmp->operate_expr->output->name,tmpexpr->if_condition_var->name)){
			 			//change the tmpexpr->if_condition_var to the list of the inputs of the compexpr or operate_expr
			 				delete tmpexpr->if_condition_var;
			 				tmpexpr->if_condition_var=NULL;
			 		
			 				tmpinput = tmp->operate_expr->input_list->first_port;
			 				while(tmpinput){
			 					node = new DeclareData;
			 					assign_value(node,tmpinput);
			 					if(!tmpexpr->if_condition_var) tmpexpr->if_condition_var = node;
			 					else Insert_var_list(tmpexpr->if_condition_var,node);
			 					tmpinput = tmpinput->next_n;
			 				}
			 			}
			 		}
			 	}
			 	//REFERENCE 3 check if it has condblock or not. if not, then convert this always node to a normal operation node EDITING HERE NOW
			 	if(!opflag){
			 		tmpinput = tmp->operate_expr->input_list->first_port;
			 		if(tmp->CondBlock){
			 			while(tmpinput){
			 				if(tmpinput == tmp->operate_expr->input_list->first_port){
			 					always_temp = new Always_block;
			 					Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,always_temp,NULL,NULL,NULL,NULL);
			 					always_temp->event_controls = new PortList;
								 Initialize_values(NULL, always_temp->event_controls,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
								 node = new DeclareData;
								assign_value(node,tmpinput);
								insert_in_list(always_temp->event_controls,node);
								always_temp->operate_expr = new Operate_node;
								Initialize_values(NULL, NULL,always_temp->operate_expr,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
								tmpexpr=NULL;
								Copy_block_to_node(tmpexpr,NULL,NULL,always_temp->operate_expr,tmp->operate_expr,true);
								Insert_between_alwayslist(tmp_position,always_temp,graph_first_node);
								 tmp_position=always_temp;
			 				}
			 				else{
			 					node = new DeclareData;
			 					assign_value(node,tmpinput);
			 					insert_in_list(always_temp->event_controls,node);
			 				}
			 				tmpinput = tmpinput->next_n;
			 			}
			 		}
			 		else{
			 			//delete the always node and transfer
			 			tmp_oper = new Operate_node;
			 			Initialize_values(NULL, NULL,tmp_oper,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
			 			tmpexpr = NULL;
			 			Copy_block_to_node(tmpexpr,NULL,NULL,tmp_oper,tmp->operate_expr,true);
			 			insert_operation_list(tmp_oper,NULL,graph_first_node);
			 			tmp_nextn = tmp->next_n;
						delete_ports_list(tmp->event_controls);
						Delete_always_node(graph_first_node,tmp,false,tmpexpr,tmpnull,true,tmp->operate_expr);
						continue;
			 		}
			 	}
			 	
			delete tmp->event_controls;
			tmp->event_controls=NULL;
		}
		if(tmp->event_controls){
			for( tnode = tmp->event_controls->first_port; tnode!=NULL ; tnode=tnode->next_n){
				loopcreate = false; prev_tr = NULL; prev_out = NULL;
				if(Search_OutputVarFrom_Places( tnode , first_place_node, prev_tr , place_node ,NULL,prev_out,graph_first_node,first_state,true,loopcreate,true) || Search_OutputVarFrom_Places( tnode , first_parallel_place, prev_tr , place_node ,NULL,prev_out,graph_first_node,first_state,true,loopcreate,true)){
					if(prev_out) tmpsearch = prev_out;
					else tmpsearch = prev_tr->output_var;
					//CHANGED HERE(loopcreate)
					if( Search_node_Loop(tmp,tmpsearch,NULL,NULL,condvar)){
						eventnotactive = true;
						loop_node = true;
						break;
					}
					else{
						eventnotactive=false;
						continue;
					}
				}
				else if( Search_var_InStateList(tnode , first_state)) //search if the signal is in the state variable list
					continue;
				else if(tnode->data_type == input) // if the signal is an input variable RULE 2
					{eventnotactive=false;continue;}
				else if(tnode->data_type == integer)
					continue;
				
				else if(!loopcreate){
					Search_varFrom_FU_Modules( graph_first_node->module_inst_node , place_node,graph_first_node,first_state,false);
					if(Search_OutputVarFrom_Places( tnode , first_place_node, prev_tr , place_node ,NULL,prev_out,graph_first_node,first_state,true,loopcreate,true) || Search_OutputVarFrom_Places( tnode , first_parallel_place, prev_tr , place_node ,NULL,prev_out,graph_first_node,first_state,true,loopcreate,true)){
						eventnotactive=false;
						continue;
					}		
				}
					eventnotactive = true;
					break;
			}
			if(!eventnotactive && (tmp->CondBlock || tmp->assign_expr || tmp->operate_expr || tmp->CaseBlock)){
			//this means all the event controls of this always node are active and the place node can be created
				attach_transition_nodes(place_node, false , tmp,graph_first_node,first_state,true,NULL,NULL,false,NULL);
				//Check for the control signals of tmp-trace them back- and insert the extra state signals 
				/*
				tmpdata = place_node->first_place_input;
				while(tmpdata){
					//assumed that the dfg only has the assignment/condop n all operationgraph has been modified into assignment already
					if(place_node->state_place_input && strcmp(tmpdata->name,place_node->first_trans_node->data_node->condition_op->assign_expr->rhs_value->name)){
						if(Trace_back_node(tmpdata,ret_state,first_state,NULL,state_list,true,true,NULL,true)){
							//compare state_list with state_place_input of the placenode. any state which is not there in state_place_input is inserted in that list
							if(place_node->state_place_input && !Check_State_list(state_list,place_node->state_place_input,place_node,10))
								statelist_edited = true;
						}
					}
					tmpdata = tmpdata->next_n;
				}
				*/
				tmp_nextn = tmp->next_n;
				/*
				if(tmp==graph_first_node->always_node) graph_first_node->always_node = tmp_nextn;
				else if(!tmp->next_n) tmp->prev_n->next_n=NULL;
				else{
					tmp->prev_n->next_n = tmp->next_n;
					tmp->next_n->prev_n = tmp->prev_n;
				}*/
				tmpexpr = NULL;
				if(tmp->CaseBlock)
					Delete_always_node(graph_first_node,tmp,true,tmpexpr,tmpnull,true,tmp_oper);
				
			}	
			else{
				delete place_node ; 
				place_node = NULL;
				tmp_nextn = tmp->next_n;
				if(loop_node) Delete_always_node(graph_first_node,tmp,true,tmpexpr,tmpnull,true,tmp_oper);	
			}

		}
		else{
			//delete the current always node
			delete place_node ; place_node = NULL;
			tmp_nextn = tmp->next_n;
			
		}
	}
	if(Check_always_node(graph_first_node->always_node))
		checkflag = false;
	//check the always node if they have any event controls or if the node doesnt have any subnodes or the input to the always node is an input, then delete the node
}

//check for the rest of the assign statements, operations and complex operations (combinational type)
//flag can be used here since its out of the FOR loop now
while(graph_first_node->varassign_node || graph_first_node->ifthenelse_node){

	Search_varFrom_FU_Modules(graph_first_node->module_inst_node ,NULL,graph_first_node,first_state,true);
	Attach_AssignNode_toDFG(NULL,true,graph_first_node,first_state,compare_op,true,true);
}

//if checkflag is false, then all always nodes have been deleted. Then now,assign and ifthenelse_nodes also are deleted. Remaining is just moduleInstantiation nodes which should be deleted. 

//RULE 7 to search and attach the clocked transitions with the previous outvars
if(first_state){
	if(first_parallel_place)
		Attach_clocked_transitions(graph_first_node,first_state,true);
	else Attach_clocked_transitions(graph_first_node,first_state,false);
}
//RULE 6
//now here, search all the vars in the petrigraph and connect them to their child nodes EDITING HERE

Delete_graph_nodes(graph_first_node);


}
}

//fn to search the nodes which ahve been created, or need not be created, and returns false if there isa node which should be created
//in this function, if the list of al_node contains a node with event controls and subnode as CondBlock/assign/CaseBlock then break and return search false. else continue search
//if search is false, then it means that the list still contains some nodes which should be created or checked.
bool Check_always_node(Always_block*& al_node){

bool search = false;
Always_block *tmpal = NULL;
Always_block *tmpal_next = NULL;
Operate_node *opernull = NULL;
ModuleInstantiate *modnull = NULL;
Ifthenelse_block *condnull = NULL;
DeclareData *var = NULL, *prev_out = NULL;
Transition_block *prev_tr = NULL;
Place_block *place_node = NULL;
Case_Statement *tmpcase = NULL;
bool loopcreate = false;


//if(search){
	tmpal = al_node;
	while(tmpal){
		tmpal_next = tmpal->next_n;
		if(!tmpal->event_controls){
			//for any condblock or assign_expr, no need to delete the always node, just send search true. it might be needed to search for loops
		//	Delete_always_node(graph_first_node,tmpal,true,condnull,modnull,true);
			search = true;
		}
		else if(tmpal->event_controls && !tmpal->CondBlock && !tmpal->CaseBlock && !tmpal->assign_expr){
			delete_ports_list(tmpal->event_controls);
			Delete_always_node(graph_first_node,tmpal,true,condnull,modnull,true,opernull);
			search = true;
		}
		//to check if tmpal has already been created, take the output of the alnode and search petri graph if its available, if yes, then delete the always node
		else if(tmpal->event_controls){
			if(tmpal->CondBlock){
				if(tmpal->CondBlock->else_expr_block){
					search = false;
					break;
				}
				else if(tmpal->CondBlock->then_expr_var) var = tmpal->CondBlock->then_expr_var->left_value;
				else if(tmpal->CondBlock->then_var) var = tmpal->CondBlock->then_var;
			}
			else if(tmpal->CaseBlock){
				tmpcase = tmpal->CaseBlock->next_n;
				var = tmpcase->expression_vt->left_value;
			}
			else if(tmpal->assign_expr)
				var = tmpal->assign_expr->left_value;
				
			if(Search_OutputVarFrom_Places(var, first_place_node, prev_tr ,place_node ,NULL,prev_out,graph_first_node,first_state,false,loopcreate,true) || Search_OutputVarFrom_Places(var,first_parallel_place,prev_tr,place_node,NULL,prev_out,graph_first_node,first_state,false,loopcreate,true)){
				search = true;
				delete_ports_list(tmpal->event_controls);
				Delete_always_node(graph_first_node,tmpal,true,condnull,modnull,true, opernull);
			}
			
			else{
				search = false;
				break;
			}	
		}
		else{
			 search = false;
			 break;
		}
		tmpal = tmpal_next;
	}
//}

return search;

}


//fn to create similar node to condexp and insert it in the conditional node list under graph_first_node
void Create_and_attach_cond(Ifthenelse_block *condexp, Graph_node *graph_first_node){

Ifthenelse_block *tmpcond = NULL;
Operate_node *tmpnull = NULL;

tmpcond = new Ifthenelse_block;
Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,tmpcond,NULL,NULL,NULL,NULL,NULL);

Copy_block_to_node(tmpcond,condexp,NULL,tmpnull,NULL,false);

insert_cond_list(tmpcond,graph_first_node);


}


//fn to delete an always node from the list in parse tree OR just delete the subnode of the always node
void Delete_always_node(Graph_node *graph_first_node,Always_block*& tmpal,bool check,Ifthenelse_block*& condblock,ModuleInstantiate*& tmpmod,bool delflag,Operate_node*& operdel){
	
Always_block *tmp_next = NULL;
Graph_node *tmpgr = NULL;
Ifthenelse_block *cond = NULL;
Ifthenelse_block *cond_next = NULL;
Case_Statement *caseexpr = NULL;
Case_Statement *caseexpr_next = NULL;
bool flag = false;

if(check){
	//if this fn is called when tmpal has CondBlock
	if(condblock)
		cond = condblock;
	else
		 cond = tmpal->CondBlock;
		
		while(cond){
			cond_next = cond->next_block;
			if(cond->if_condition_var){
				Delete_var_node(cond->if_condition_var);
				//delete cond->if_condition_var;
				//cond->if_condition_var = NULL;
			}
			if(cond->equal_condition){
				Delete_var_node(cond->equal_condition->left_value);
				delete cond->equal_condition;
				cond->equal_condition = NULL;
			}
			if(cond->then_var){
				Delete_var_node(cond->then_var);
				
			}
			else if(cond->then_expr_var){
				Delete_var_node(cond->then_expr_var->left_value);
				Delete_var_node(cond->then_expr_var->right_value);
			
				delete cond->then_expr_var;
				cond->then_expr_var = NULL;
			}
			
			if(tmpal && cond == tmpal->CondBlock)
				tmpal->CondBlock = cond_next;
			else if(condblock && cond == condblock)
				condblock = cond_next;
			else if(!cond->next_block)
				cond->prev_block->next_block = NULL;
			else{
				cond->prev_block->next_block = cond->next_block;
				cond->next_block->prev_block = cond->prev_block;
			}
			delete cond;
			cond = NULL;
			if(condblock)
				break;
			
			cond = cond_next;
		}
	if(tmpal->CaseBlock){
		caseexpr = tmpal->CaseBlock;
		while(caseexpr){
			caseexpr_next = caseexpr->next_n;
			
			if(caseexpr->condition_var)
				Delete_var_node(caseexpr->condition_var);
			if(caseexpr->expression_vt){
				Delete_var_node(caseexpr->expression_vt->right_value);
				Delete_var_node(caseexpr->expression_vt->left_value);
			}
			delete caseexpr; caseexpr = NULL;
			
			caseexpr = caseexpr_next;
		}
	}
	if(tmpal->assign_expr){
		Delete_var_node(tmpal->assign_expr->left_value);
		Delete_var_node(tmpal->assign_expr->right_value);
		delete tmpal->assign_expr;
		tmpal->assign_expr = NULL;
	}
		
	if(delflag){
		tmp_next = tmpal->next_n;
		
		if(tmpal == graph_first_node->always_node)
			graph_first_node->always_node = tmp_next;
	
		else if(!tmpal->next_n)
			tmpal->prev_n->next_n = NULL;
		else{
			tmpal->prev_n->next_n = tmpal->next_n;
			tmpal->next_n->prev_n = tmpal->prev_n;
		}
		
		delete tmpal;
		tmpal = NULL;
	}
}
else if(!check && !operdel){
	if(tmpmod == graph_first_node->module_inst_node)
		graph_first_node->module_inst_node = tmpmod->nextm;
	else if(!tmpmod->nextm)
		tmpmod->prevm->nextm = NULL;
	else{
		tmpmod->prevm->nextm = tmpmod->nextm;
		tmpmod->nextm->prevm = tmpmod->prevm;
	}
	/*
	for(tmpgr = graph_first_node ; tmpgr!=NULL;tmpgr = tmpgr->next_node){
		if(!strcmp(tmpgr->name,tmpmod->mod_name)){
			flag = true;
			break;
		}
	}
	if(flag){
		if(!tmpgr->next_node)
			tmpgr->prev_node->next_node = NULL;
		else{
			tmpgr->prev_node->next_node = tmpgr->next_node;
			tmpgr->next_node->prev_node = tmpgr->prev_node;
		}
		if(tmpgr->operation_node){
			delete_var_list(NULL,tmpgr->operation_node->input_list->first_port);
			delete tmpgr->operation_node->input_list;
			tmpgr->operation_node->input_list = NULL;
			Delete_var_node(tmpgr->operation_node->output);
			delete tmpgr->operation_node;
			tmpgr->operation_node = NULL;
		}
		delete tmpgr;
		tmpgr = NULL;
	}
	*/
	
	delete_var_list(NULL,tmpmod->ports_list->first_port);
	delete tmpmod->ports_list;
	tmpmod->ports_list = NULL;
	
	delete tmpmod;
	tmpmod = NULL;
}
else if(!check && operdel){
	delete_var_list(NULL,operdel->input_list->first_port);
	delete operdel->input_list;
	operdel->input_list = NULL;
	delete operdel->output;
	operdel->output = NULL;
	delete operdel;
	operdel = NULL;
	if(delflag){
		tmp_next = tmpal->next_n;
		if(tmpal == graph_first_node->always_node)
			graph_first_node->always_node = tmp_next;
	
		else if(!tmpal->next_n)
			tmpal->prev_n->next_n = NULL;
		else{
			tmpal->prev_n->next_n = tmpal->next_n;
			tmpal->next_n->prev_n = tmpal->prev_n;
		}
		
		delete tmpal;
		tmpal = NULL;
	}
	
}
	
}

//fn to delete the subnodes of the graph node remaining if they are not deleted until now. and also delete the next_nodes after graph_first_node
void Delete_graph_nodes(Graph_node *graph_first_node){


Graph_node *tmpg = NULL;
Graph_node *tmpg_next = NULL;
DeclareData *tmp = NULL, *tmp_n = NULL;
Always_block *tmpal = NULL, *tmpal_n=NULL;
ModuleInstantiate *mod = NULL, *mod_n = NULL;
Ifthenelse_block *cond = NULL;
Operate_node *tmpop = NULL, *tmpop_n = NULL , *tmpnull = NULL;


tmpg = graph_first_node;

while(tmpg){
	tmpg_next = tmpg->next_node;
	if(tmpg->data_node){
		tmp = tmpg->data_node;
		while(tmp){
			tmp_n = tmp->next_n;
			if(tmp == tmpg->data_node){
				//tmp->next_n->prev_n = NULL;
				tmpg->data_node = tmp->next_n;
			}
			else if(!tmp->next_n)
				tmp->prev_n->next_n = NULL;
			else{
				tmp->prev_n->next_n = tmp->next_n;
				tmp->next_n->prev_n = tmp->prev_n;
			}
			Delete_var_node(tmp);
			tmp = tmp_n;
		}
	}
	if(tmpg->always_node){
		tmpal = tmpg->always_node;
		while(tmpal){
			cond = NULL;mod = NULL;
			tmpal_n = tmpal->next_n;
			Delete_always_node(graph_first_node,tmpal,true,cond,mod,true,tmpnull);
			tmpal = tmpal_n;
		}
	}
	if(tmpg->module_inst_node){
		mod = tmpg->module_inst_node;
		while(mod){
			cond = NULL;tmpal = NULL;
			mod_n = mod->nextm;
			Delete_always_node(graph_first_node,tmpal,false,cond,mod,false,tmpnull);
			mod = mod_n;
		}
	}
	if(tmpg->operation_node){
		tmpop = tmpg->operation_node;
		while(tmpop){
			tmpop_n = tmpop->next_op;
			tmp = tmpop->input_list->first_port;
			while(tmp){
				tmp_n = tmp->next_n;
				if(tmp == tmpop->input_list->first_port){
					//tmp->next_n->prev_n = NULL;
					tmpop->input_list->first_port = tmp->next_n;
				}
				else if(!tmp->next_n)
					tmp->prev_n->next_n = NULL;
				else{
					tmp->prev_n->next_n = tmp->next_n;
					tmp->next_n->prev_n = tmp->prev_n;
				}
				Delete_var_node(tmp);
				tmp = tmp_n;
			}
			delete tmpop->input_list; tmpop->input_list = NULL;
			
			Delete_var_node(tmpop->output);
			
			if(tmpop == tmpg->operation_node){
				//tmpop->next_op->prev_op = NULL;
				tmpg->operation_node = tmpop->next_op;
			}
			else if(!tmpop->next_op)
				tmpop->prev_op->next_op = NULL;
			else{
				tmpop->prev_op->next_op = tmpop->next_op;
				tmpop->next_op->prev_op = tmpop->prev_op;
			}
			delete tmpop; tmpop = NULL;
			tmpop = tmpop_n;
		}
	}
	if(tmpg == graph_first_node){
		//tmpg->next_node->prev_node = NULL;
		graph_first_node = tmpg->next_node;
	}
	else if(!tmpg->next_node)
		tmpg->prev_node->next_node = NULL;
	else{
		tmpg->prev_node->next_node = tmpg->next_node;
		tmpg->next_node->prev_node = tmpg->prev_node;
	}
	delete tmpg ; tmpg = NULL;

	tmpg = tmpg_next;
}



}




//function to create the dfgs from FU modules only if both the inputs are already inserted in the graph created until this point

void Search_varFrom_FU_Modules( ModuleInstantiate *mod_node , Place_block *plnode,Graph_node *graph_first_node,State_var *first_state,bool delflag){


ModuleInstantiate *tmpmod = NULL ,  *tmpmod_nextm = NULL;
DeclareData *node = NULL , *dnode1=NULL , *dnode2=NULL ,*newdata=NULL ,*prev_outvar =NULL , *tmpnull = NULL , *tmpdnode = NULL , *output=NULL , *statecheck=NULL;
bool search = false , nodeready=true,checkflag=false,loopcreate = false;
Always_block *tmpl = NULL;
Operate_node *tmpnull_op = NULL;
Ifthenelse_block *tmpcond = NULL;
Graph_node *gnode = NULL , *gnode_next=NULL;
DFG_block *dfg_search = NULL;
Place_block *newplace=NULL , *newplace1=NULL;
Transition_block *prevtr = NULL; 
Compare_operator *compare_op = NULL;
//dnode1 is from modinstantiation node
//dnode2 is from gnode which is the main FU node


for(tmpmod = mod_node ; tmpmod!=NULL ; tmpmod = tmpmod_nextm){

	for(gnode = graph_first_node->next_node;gnode!=NULL;gnode = gnode->next_node){
		if(!strcmp(tmpmod->mod_name,gnode->name)){
			if(gnode->operation_node)
				Select_from_operator_list(NULL,tmpmod, gnode->operation_node->operator_type);
			break;
		}
	}

		if(!strcmp(tmpmod->mod_name , gnode->name)){
			if(gnode->operation_node)
				tmpdnode = gnode->operation_node->input_list->first_port;
			else if(gnode->always_node)
					tmpdnode = gnode->data_node;
			
			for(dnode1=tmpmod->ports_list->first_port , dnode2=tmpdnode; dnode1->next_n!=NULL; dnode1=dnode1->next_n , dnode2=dnode2->next_n){
				checkflag=false;
				
				Attach_AssignNode_toDFG(dnode1,false,graph_first_node,first_state,compare_op,false,false);
				
					 if(dnode1->data_type==integer){
						/*nodeready=true;*/ dnode2->name = dnode1->name;}
					
					else if(dnode2->data_type==integer){
						
						if(Search_OutputVarFrom_Places( dnode1 , first_place_node , prevtr ,  newplace/*null*/ , dfg_search , prev_outvar,graph_first_node,first_state,true,loopcreate,true) || Search_output_from_node_list(dnode1)){
							if(prev_outvar && Search_node_Loop(NULL,prev_outvar,tmpmod,NULL,tmpnull) || (prevtr && Search_node_Loop(NULL,prevtr->output_var,tmpmod,NULL,tmpnull))){
								nodeready = false;
								break;
							}
							else nodeready = true;
						}
						else	nodeready=false;
						//CHANGE 1
						newdata = new DeclareData;
						assign_value(newdata , dnode2);
						newdata->data_type=integer;
						newdata->next_n = dnode1->next_n;
						newdata->prev_n = dnode1;
						dnode1->next_n = newdata;
					}
					else if(dnode1->data_type!=integer && (Search_OutputVarFrom_Places( dnode1 , first_place_node , prevtr ,  newplace/*null*/ , dfg_search , prev_outvar,graph_first_node,first_state,true,loopcreate,true) || Search_OutputVarFrom_Places(dnode1,first_parallel_place,prevtr,newplace,dfg_search,prev_outvar,graph_first_node,first_state,true,loopcreate,true) || Search_output_from_node_list(dnode1))){
					//check if both the input signals are in the same state
					//RULE 1
						if(prev_outvar && Search_node_Loop(NULL,prev_outvar,tmpmod,NULL,tmpnull) || (prevtr && Search_node_Loop(NULL,prevtr->output_var,tmpmod,NULL,tmpnull))){
							nodeready = false;
							break;
						}
						checkflag=true;
						nodeready = true;dnode2->name = dnode1->name;
						/*
						if(first_state && dnode1->prev_n && dnode1->prev_n->data_type!=integer){
						
							 newplace = Search_place_of_input(first_state,true,NULL,dnode1->prev_n,output); //previous input's place
							if(newplace){
							//state_place_input is the list of state signals in newplace, placenode of the previous input
								newplace1 = Search_place_of_input(first_state,true,NULL, dnode1,output); //second input's place	
								if(newplace->state_place_input){ //check only if the place has a state input
									if( Check_state_of_input(newplace,newplace1))
								
										{nodeready=true; dnode2->name = dnode1->name;}
									else
										 {nodeready = false ; break;}
								} 
								else{ //if there is no state input to the place
									 nodeready=true; dnode2->name = dnode1->name;
								}				
							}
							
						}	
					
						else {nodeready=true; dnode2->name = dnode1->name;}
						*/
					}
					else if(!checkflag && dnode1->data_type!=integer){
					 //search in the equalto nodes
					 	if(Search_in_equalto_list(dnode1,output)){
					 		nodeready=true; dnode2->name = dnode1->name;
					 	}
						else {nodeready = false ; break;} 	
					}
					else {nodeready = false ; break;}	
			}
		
					
			if(nodeready){
				DFG_block *dfg_node = new DFG_block;
				Initialize_structures(NULL, dfg_node,NULL,NULL,NULL,NULL);
				Create_DFG_from_FU(gnode , dfg_node , plnode , tmpmod,graph_first_node,first_state );
				// search to connect the output var with the clock transition nodes
				if(first_place_node)
					Search_outputvar_from_ClockTransition(dfg_node);
				
				//NO DELETING THE MODNODES FOR NOW
				tmpmod_nextm = tmpmod->nextm;
				//gnode_next = gnode->next_node;
				
				//Delete the modnodes only if delflag is true,this happens only at the end of the while loop in main function
				//tmpcond,tmpl is null
				if(delflag) Delete_always_node(graph_first_node,tmpl,false,tmpcond,tmpmod,false,tmpnull_op);
				
			}	
			else{
				//if(newdata)
				//	delete newdata; newdata = NULL;  //CHANGED HERE
				
				tmpmod_nextm = tmpmod->nextm;
			}
			//delete the datanode of this gnode			
		}
		else{
			tmpmod_nextm = tmpmod->nextm;
			
		}

}
	//try to attach the remaining equal nodes
	Attach_AssignNode_toDFG(NULL,false,graph_first_node,first_state,compare_op,false,false);
	

}
	
	
	
//function to search previous input's place	
//flag is to indicate if fn is called externally or internally. if flag is true,its called externally and state is used to check the graph else, the fn is continued from place_n, which is sent internally inside the fn
Place_block *Search_place_of_input(State_var *state,bool flag,Place_block *place_n,DeclareData *input,DeclareData*& outvar, bool nodeflag,DeclareData *tmpvar){

// the input variable, must have a place input
Transition_block *tran = NULL;
Place_block *placetemp=NULL,*plnode=NULL;
State_var *tmpstate = NULL;
Equal_to_op *tmpeq= NULL;
bool search = false ,node = false;
Operate_op *opnext , *opnext_s = NULL;
DeclareData *var , *var_s , *vart = NULL;

if(flag)
	tmpstate = state;
else if(!flag && !nodeflag)
	tran = place_n->first_trans_node;
else if(nodeflag)
	var = tmpvar;



while(var || tmpstate || tran){
	if(flag && !node) var = tmpstate->state_name;
	else if(!node && !nodeflag) var = tran->output_var;
	//else if(nodeflag) var = tmpvar;
	node = false;

	if(!flag && !strcmp(var->name , input->name)){
		placetemp = place_n;
		outvar = tran->output_var;
		search = true;
		break;
	}
	 if(var->place_ptr){
		plnode =var->place_ptr;
		node = true;
		while(plnode){
			placetemp = Search_place_of_input(tmpstate,false,plnode , input,outvar,false,NULL);
			if(placetemp){
				search=true;
				break;
			}
		plnode = plnode->next_place;
		}
		if(search) break;
		else node = false;
	}
	if(!node && var->transition_out){
		node = true;
		vart = var->transition_out->output_var;
		while(vart && vart->place_ptr){
			placetemp = Search_place_of_input(tmpstate,false,vart->place_ptr,input,outvar,false,NULL);
			if(placetemp){
				search = true;
				break;
			}
			else if(vart->transition_out) vart = vart->transition_out->output_var;
			else vart = NULL;
		}
		if(search) break;
		else var = vart;
	}
	if(!node && var->operator_out){
		node = true;
		opnext = var->operator_out;
	
			var_s = opnext->output_value;
			while(var_s && var_s->place_ptr){
				placetemp = Search_place_of_input( tmpstate,false,var_s->place_ptr,input,outvar,false,NULL);
				if(placetemp){
					search=true;
					break;
				}
				else if(var_s->operator_out) var_s = var_s->operator_out->output_value;
				else var_s = NULL;
			}
			if(search) break;
			else var = var_s;
	}
	if(!node && var->equal_op_out){
		node = true;
		tmpeq = var->equal_op_out;
		while(tmpeq){
			vart = tmpeq->lhs_value;
			if(vart && vart->place_ptr && Search_place_of_input(tmpstate,false,vart->place_ptr,input,outvar,false,NULL)){
				search = true;
				break;
			}
			else if(vart && vart->equal_op_out && Search_place_of_input(tmpstate,false,NULL,input,outvar,true,vart)){ //var = vart->equal_op_out->lhs_value;
				search = true;
				break;
			}
			else var = NULL;
			tmpeq = tmpeq->next_equal;
		}
		/*
		while(vart && vart->place_ptr){
			placetemp = Search_place_of_input( tmpstate,false,vart->place_ptr,input,outvar);
			if(placetemp){
				search=true;
				break;
			}
			else if(vart->equal_op_out) vart = vart->equal_op_out->lhs_value;
			else vart = NULL;
		} */
		if(search) break;
		//else var = vart;
		
	}
		
			
if(!search && !node){
	if(flag) tmpstate = tmpstate->next_state;
	else
		tran = tran->next_trans_node;	
}

		
	
} //end of while

//check the parallel place  nodes
if(!search){

	place_n = first_parallel_place;
	while(place_n){
		placetemp = Search_place_of_input(NULL,false,place_n,input,outvar,false,NULL);
		if(placetemp){
			search=true;
			break;
		}
	place_n = place_n->next_place;
	}
}

return placetemp;
}


//to check if both input signals of FU are from the same state
bool Check_state_of_input(Place_block *firstplace , Place_block *secondplace){

DeclareData *tmp=NULL;
DeclareData *tmp1 = NULL;
bool check=false;

if(firstplace->state_place_input && secondplace->state_place_input){

	for(tmp=firstplace->state_place_input ; tmp!=NULL; tmp = tmp->next_n){
	
		for(tmp1= secondplace->state_place_input ; tmp1!=NULL; tmp1=tmp1->next_n){
		
			if(!strcmp(tmp1->name, tmp->name)){
				check=true;
				break;
			}
		} 
	}

}
else check = false;

return check;

}


			
//function to connect the output var of dfg's to the input variable of only "clocked" transition nodes
void Search_outputvar_from_ClockTransition(DFG_block *dfg_node){


Transition_block *tmp=NULL;
Operate_op *tmpop=NULL;

tmp= first_place_node->first_trans_node;

while(tmp){
	if(tmp->data_node->assignment_graph){
	
		if(!strcmp(dfg_node->output->name,tmp->data_node->assignment_graph->rhs_value->name)){
			if(!dfg_node->output->transition_out) dfg_node->output->transition_out = tmp;
			//else Insert_in_output_transition_list(dfg_node->output,tmp);
			if(dfg_node->operation_graph) 
				dfg_node->operation_graph->output_value->transition_out = tmp;
				break;
		}
	}
	/*else if(tmp->data_node->operation_graph){
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
	}*/

tmp = tmp->next_trans_node;
}
		


}

//PUT function here
//condexp is sent when ifthenelse block is to be created,in node_al,there may be multiple condexp, in that case create only one condexp, else if condexp is null, then create the entire node_al

void attach_transition_nodes(Place_block *placenode, bool attach_nullalways , Always_block *node_al,Graph_node *graph_first_node,State_var *first_state,bool loopflag,DeclareData *endvar,Ifthenelse_block *condexp ,bool search_async,DeclareData *inputvar){


Always_block *temp = NULL;
DeclareData *cnode =NULL , *in_node=NULL , *prev_out=NULL , *dnode=NULL, *varassign = NULL;
Operate_node *operassign = NULL;
Transition_block *prev_tr=NULL , *transnode = NULL;
State_var *stateinput=NULL;
bool loopcreate = false , attach = false;

if(attach_nullalways){
	
	if(!placenode) 
		first_place_node->next_trans_node = true;
	first_place_node->first_place_input = NULL;
	for( temp = first_null_always_node ; temp!=NULL; temp = temp->next_n){
		
		transnode = new Transition_block;
		Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,transnode);
		// select cases for different types of always node
		Create_node_in_Transition_block(&transnode , temp,graph_first_node,first_state,attach_nullalways,true,NULL,condexp,NULL);
		transnode->own_place_ptr = first_place_node;
		if(temp==first_null_always_node)
		first_place_node->first_trans_node = transnode;
		else
		Insert_in_transition_list(&transnode , first_place_node);
	}
	if(!graph_first_node->always_node){
		delete first_place_node;
		first_place_node = NULL;
	}
		
}		

else{
	
	transnode = new Transition_block;
	Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,transnode);
	//EDITING HERE
	if(search_async && node_al->CondBlock && !condexp && Search_assign_list(node_al->CondBlock->if_condition_var,graph_first_node,varassign,operassign)){
		if(varassign)
			Replace_ports_list(node_al,node_al->event_controls,varassign,true,NULL,graph_first_node);
		else if(operassign)
			Replace_ports_list(node_al,node_al->event_controls,varassign,false,operassign,graph_first_node);
		
	}
	
	Create_node_in_Transition_block(&transnode , node_al,graph_first_node,first_state,attach_nullalways,loopflag,endvar,condexp,inputvar);
	//if(endvar) endvar->place_ptr = placenode;
	transnode->own_place_ptr = placenode;
	
	
	//check if the placenode is newly created or already is active
	if( !placenode->first_trans_node)
	{
		placenode->first_trans_node = transnode;
		placenode->token_active = true;
		placenode->next_trans_node = false;
		for(cnode = node_al->event_controls->first_port ; cnode!=NULL; cnode=cnode->next_n){
			prev_tr=NULL;prev_out=NULL; stateinput = NULL;
			if(condexp && !Search_in_Cond_Block(cnode,condexp))
				continue;
			if( Search_OutputVarFrom_Places( cnode , first_place_node, prev_tr , placenode ,NULL,prev_out,graph_first_node,first_state,loopflag,loopcreate,true) || Search_OutputVarFrom_Places( cnode , first_parallel_place, prev_tr , placenode ,NULL,prev_out,graph_first_node,first_state,loopflag,loopcreate,true) || Search_var_InStateList(cnode,first_state) || (cnode->data_type==input)){
				if(prev_tr ){
					prev_tr->outgoing_external_place = placenode;
					if(!prev_tr->output_var->place_ptr) prev_tr->output_var->place_ptr = placenode;
					else Insert_place_in_list(prev_tr->output_var,placenode);
				}
				else if(prev_out){
					if(!prev_out->place_ptr) prev_out->place_ptr = placenode;
					else Insert_place_in_list(prev_out,placenode);
				}
				//for state signals
				else if(Search_var_from_statelist(cnode,stateinput,false)){
					if(!placenode->state_place_input) placenode->state_place_input = stateinput->state_name;
					else Insert_placeInput_list(placenode,stateinput->state_name,false);
					//to insert a place under a state node
					if(!stateinput->state_name->place_ptr) stateinput->state_name->place_ptr = placenode;
					else  Insert_place_in_list(stateinput->state_name,placenode);
					
				}
				
				if(!placenode->first_place_input){
					if(prev_tr){
					 placenode->first_place_input = prev_tr->output_var;
					 }
					else if(prev_out){
					 placenode->first_place_input = prev_out;
					
					 }
					else if(cnode->data_type==input){ //for input signals
						placenode->first_place_input = new DeclareData;
						assign_value(placenode->first_place_input,cnode);
						placenode->first_place_input->place_ptr = placenode;
						Insert_in_parallel_place_list(placenode);
					}
					
				}
				else{

					if(prev_tr){
						Insert_placeInput_list(placenode , prev_tr->output_var,true);
						//if(!prev_tr->output_var->place_ptr) prev_tr->output_var->place_ptr = placenode;
					//	 else Insert_place_in_list(prev_tr->output_var,placenode);
					}
					else if(prev_out){
						 Insert_placeInput_list(placenode , prev_out,true);
					//  if(!prev_out->place_ptr) prev_out->place_ptr = placenode;
					// else Insert_place_in_list(prev_out,placenode);
					 }
					else if(cnode->data_type==input){ //for input signal
						dnode = new DeclareData;
						assign_value(dnode,cnode);
						dnode->place_ptr = placenode;
						Insert_placeInput_list(placenode,dnode,true);
						Insert_in_parallel_place_list(placenode);
					}
				
				}
			}
			else if(cnode->data_type == integer)
				continue;
			//if endvar is available
			else if(endvar && !attach){
				if(!placenode->first_place_input) placenode->first_place_input = endvar;
				else Insert_placeInput_list(placenode,endvar,true);
				attach = true;
			}
			else{
				 //var_char[char_num++] = cnode->name;
				 dnode = new DeclareData;
				 assign_value(dnode, cnode);
				 dnode->place_ptr = placenode;
				 Insert_placeInput_list(placenode,dnode,true);
				 varinput_list[list_num++] = dnode;
			}
		}
		
		//if(transnode->data_node->condition_op->switchcase)
			//Insert_datainput_in_placelist(transnode);
	}
	else{
		placenode->next_trans_node = true;
		transnode->traverse_node = true;
		Insert_in_transition_list(&transnode , placenode);
		//if(transnode->data_node->condition_op->switchcase)
			//Insert_datainput_in_placelist(transnode);
	}
	
			
}

}

//function to attach another place node below attachvar
void Insert_place_in_list(DeclareData *attachvar , Place_block *place_ins){

Place_block *tmp = NULL;
for(tmp = attachvar->place_ptr; tmp->next_place!=NULL; tmp = tmp->next_place);
tmp->next_place = place_ins;
place_ins->next_place = NULL;
}

/*
void Insert_datainput_in_placelist(Transition_block *transnode,bool &flag,Graph_node *graph_first_node,State_var *first_state){

Condition_block *tmp=NULL;
//DeclareData *tmpvar = transnode->own_place_ptr->first_place_input;
DeclareData *prev_out=NULL;
Transition_block *prev_tr=NULL;
Place_block *placenode=NULL;
bool loopcreate = false;

tmp = transnode->data_node->condition_op;

while(tmp){
	prev_out = NULL;prev_tr = NULL;
	if(tmp->assign_expr && Search_OutputVarFrom_Places( tmp->assign_expr->rhs_value, first_place_node, prev_tr , placenode ,NULL,prev_out,graph_first_node,first_state,true,loopcreate)){
		
		if(prev_tr){
		 prev_tr->outgoing_external_place = transnode->own_place_ptr;
		 Insert_placeInput_list(transnode->own_place_ptr ,prev_tr->output_var,true);
		 }
		else if(prev_out) {
		 prev_out->place_ptr = transnode->own_place_ptr;
		 Insert_placeInput_list(transnode->own_place_ptr, prev_out,true);
		 }
		 flag = true;
		
	}
	else flag = false;
	
tmp = tmp->next_cond;

}

}
*/

//function to insert placnode in the list of parallel place nodes
void Insert_in_parallel_place_list(Place_block *node){

Place_block *tmp=NULL;

if(!first_parallel_place){
	first_parallel_place = node;
	node->next_place=NULL;
}
else{
	for(tmp = first_parallel_place ; tmp->next_place!=NULL;tmp = tmp->next_place);
	tmp->next_place = node;
	node->next_place = NULL;
}

}

//function to search node in one of the input elements of conditional_exp
bool Search_in_Cond_Block(DeclareData *node, Ifthenelse_block *conditional_exp){

bool search = false;

if(conditional_exp->if_condition_var && !strcmp(node->name, conditional_exp->if_condition_var->name))
	search = true;
if(conditional_exp->equal_condition && !strcmp(node->name, conditional_exp->equal_condition->left_value->name))
	search = true;
if(conditional_exp->then_expr_var && (!strcmp(node->name,conditional_exp->then_expr_var->right_value->name) || !strcmp(node->name,conditional_exp->then_expr_var->left_value->name)))
	search = true;
	
	
return search;
}


// function to create different kinds of DFG's in a transition block irrespective of it is in nullalways list or not

void Create_node_in_Transition_block( Transition_block **CurrentTransNode  , Always_block *temp,Graph_node *graph_first_node,State_var *first_state,bool attach_nullalways,bool loopflag,DeclareData *endvar,Ifthenelse_block *condcheck,DeclareData *input_var){

Transition_block *prev_tr = NULL;
DeclareData *prev_out = NULL;
bool output_exists = false , loopcreate = false;
Place_block *placenode = NULL;


if(temp->CaseBlock)
{
	(*CurrentTransNode)->data_node = new DFG_block;
	Initialize_structures(NULL, (*CurrentTransNode)->data_node,NULL,NULL,NULL,NULL);
	if(Search_OutputVarFrom_Places( temp->CaseBlock->next_n->expression_vt->left_value, first_place_node, prev_tr , placenode ,NULL,prev_out,graph_first_node,first_state,false,loopcreate,true)){
		if(prev_tr)
			(*CurrentTransNode)->output_var = prev_tr->output_var;
		else if(prev_out)
			(*CurrentTransNode)->output_var = prev_out;
		output_exists = true;
	}
	else{
		(*CurrentTransNode)->output_var = new DeclareData;
		Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL, (*CurrentTransNode)->output_var,NULL,NULL,NULL);
	}
	Create_DFG_from_Caseblock( (*CurrentTransNode)->data_node, temp->CaseBlock , (*CurrentTransNode)->output_var,graph_first_node,first_state,loopflag,endvar,output_exists,input_var);
	//take the lhs value of any condition_block->assign_expr as output_var
	
	//connect the output of this dfg to the input var of any of the "clocked"transitions if available
	Search_outputvar_from_ClockTransition((*CurrentTransNode)->data_node);
	
			
}	
	
else if(temp->assign_expr)
{
	(*CurrentTransNode)->data_node = new DFG_block;
	Initialize_structures(NULL, (*CurrentTransNode)->data_node,NULL,NULL,NULL,NULL);
	//(*CurrentTransNode)->output_var = new DeclareData;
	//Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL, (*CurrentTransNode)->output_var,NULL,NULL,NULL);
	Create_DFG_from_assignexpr( (*CurrentTransNode)->data_node , temp->assign_expr , (*CurrentTransNode)->output_var,graph_first_node,first_state,attach_nullalways,loopflag);
	if(attach_nullalways)
		(*CurrentTransNode)->data_node->assignment_graph->rhs_value->transition_out = (*CurrentTransNode);
	//connect the output of this dfg to the input var of any of the "clocked"transitions if available
	Search_outputvar_from_ClockTransition((*CurrentTransNode)->data_node);


}


else if(temp->operate_expr)

{
	(*CurrentTransNode)->data_node = new DFG_block;
	Initialize_structures(NULL, (*CurrentTransNode)->data_node,NULL,NULL,NULL,NULL);
	(*CurrentTransNode)->output_var = new DeclareData;
	Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL, (*CurrentTransNode)->output_var,NULL,NULL,NULL);
	if( temp->operate_expr && !temp->comp_expr)
		Create_DFG_from_operateexpr( (*CurrentTransNode)->data_node , temp->operate_expr , (*CurrentTransNode)->output_var,true,true);
		//Create_DFG_from_operateexpr();
	else if(temp->comp_expr)
		Create_DFG_from_complexexpr( (*CurrentTransNode)->data_node, temp , (*CurrentTransNode)->output_var);
		
	//connect the output of this dfg to the input var of any of the "clocked"transitions if available
	Search_outputvar_from_ClockTransition((*CurrentTransNode)->data_node);

}

else if(temp->CondBlock)

	// to create the condition block function
{
	(*CurrentTransNode)->data_node = new DFG_block;
	Initialize_structures(NULL, (*CurrentTransNode)->data_node,NULL,NULL,NULL,NULL);
	//CHANGED HERE (!endvar)
	if(Search_OutputVarFrom_Places( temp->CondBlock->then_expr_var->left_value , first_place_node, prev_tr , placenode ,NULL,prev_out,graph_first_node,first_state,false,loopcreate,true)){
		if(prev_tr)
			(*CurrentTransNode)->output_var = prev_tr->output_var;
		else if(prev_out)
			(*CurrentTransNode)->output_var = prev_out;
		output_exists = true;
	}
	else{	
		(*CurrentTransNode)->output_var = new DeclareData;
		Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL, (*CurrentTransNode)->output_var,NULL,NULL,NULL);
	}
	Create_DFG_from_ifthenelse( (*CurrentTransNode)->data_node, temp->CondBlock , (*CurrentTransNode)->output_var,graph_first_node,first_state,loopflag,endvar,condcheck,output_exists);
	

	//connect the output of this dfg to the input var of any of the "clocked"transitions if available
	Search_outputvar_from_ClockTransition((*CurrentTransNode)->data_node);
}

}


//function to insert the input to a place in its input list

void Insert_placeInput_list( Place_block *place_active , DeclareData *dnode,bool placeorstate){

DeclareData *temp_n = NULL;

if(placeorstate){
	for(temp_n = place_active->first_place_input ; temp_n->next_n!=NULL; temp_n=temp_n->next_n);
	temp_n->next_n = dnode;
	dnode->prev_n = temp_n;
	dnode->next_n=NULL;

}
else{
	temp_n = place_active->state_place_input;
	for(temp_n;temp_n->next_n!=NULL;temp_n=temp_n->next_n);
	temp_n->next_n = dnode;
	dnode->prev_n = temp_n;
	dnode->next_n=NULL;
		
}
}


//function to attach a variable tmp to its successive node which may be opertmp,placenode,equaltmp or compare_tmp.
//tmp is already created in petrigraph
void Attach_first_node_in_Loop(DeclareData*& tmp,struct PathList_struct *first_node){

DFG_block *datanode = NULL;

if(first_node->placenode){
	if(!tmp->place_ptr) tmp->place_ptr = first_node->placenode;
	else Insert_place_in_list(tmp , first_node->placenode);
	if(!first_node->placenode->first_place_input) first_node->placenode->first_place_input = tmp;
	else Insert_placeInput_list(first_node->placenode,tmp,true);
	datanode = first_node->placenode->first_trans_node->data_node;
	if(datanode->assignment_graph)
		datanode->assignment_graph->rhs_value = tmp;
	else if(datanode->condition_op){
		if(!datanode->condition_op->if_cond_var) datanode->condition_op->if_cond_var = tmp;
		else if(!datanode->condition_op->assign_expr->rhs_value) datanode->condition_op->assign_expr->rhs_value = tmp; 
	}
	
}
else if(first_node->trannode){
	if(!tmp->transition_out) tmp->transition_out = first_node->trannode;
	
}
else if(first_node->eqnode){
	if(!tmp->equal_op_out) tmp->equal_op_out = first_node->eqnode;
	else Insert_in_equalto_list(NULL,tmp, first_node->eqnode);
	first_node->eqnode->rhs_value = tmp;
}
else if(first_node->opnode){
	tmp->operator_out = first_node->opnode;
	if(!first_node->opnode->op1) first_node->opnode->op1 = tmp;
	else first_node->opnode->op2 = tmp;

}
else if(first_node->compnode){
	if(!first_node->compnode->condition_value) first_node->compnode->condition_value = tmp;
	
}



}


//function to search if nodesearch i.e an always node has already been created following varstart
//this fn is called only for checking an always node. thus 
//this fn should also check the inputs as well as the outputs and both must be the same for always block/FU module/ assign node
//here the nodesearch wil be searched further only if any subnodes of the nodesearch exist, otherwise search is false
bool Search_node_Loop(Always_block *nodesearch, DeclareData *varstart,ModuleInstantiate *modn,Assign_var *equalnode,DeclareData*& value){

DeclareData *tmp = NULL,*tmpd = NULL,*tmpst = NULL,*tmpout = NULL;
Place_block *tmp_pl = NULL;
Equal_to_op *eqtemp = NULL;
Case_Statement *casebl = NULL;
bool search = false;

if(nodesearch && (nodesearch->CaseBlock || nodesearch->CondBlock || nodesearch->assign_expr || nodesearch->operate_expr)){
	 if(nodesearch->CaseBlock){
		 casebl = nodesearch->CaseBlock->next_n;
		 tmpd = casebl->expression_vt->left_value;
		 	 
	 }
	 else if(nodesearch->CondBlock){
		 if(nodesearch->CondBlock->then_expr_var)
		 	 tmpd = nodesearch->CondBlock->then_expr_var->left_value;
		 else tmpd = nodesearch->CondBlock->then_var;
	 }
	else if(nodesearch->assign_expr)
	 	tmpd = nodesearch->assign_expr->left_value;
	
	
	
	if(varstart->place_ptr){
	
		tmp_pl = varstart->place_ptr;
		while(tmp_pl){
			tmp = nodesearch->event_controls->first_port;
			tmpout = tmp_pl->first_trans_node->output_var;
			//node = true;
			while(tmp){
				tmpst = tmp_pl->first_place_input;
				while(tmpst){
					if(!strcmp(tmpst->name,tmp->name)){
						if(!strcmp(tmpout->name,tmpd->name)){
							search = true;
							break;
						}
						else search = false;
					}
					else search = false;
					tmpst = tmpst->next_n; 
				}
				/*
				tmpst = tmp_pl->state_place_input;
				while(!search && tmpst){
					if(!strcmp(tmpst->name,tmp->name)){
						search = true;
						break;
					}
					tmpst = tmpst->next_n;
				}*/
				
				if(!search)
					 tmp = tmp->next_n;
				
				else tmp = NULL;	
			}
			if(search) break;
			tmp_pl = tmp_pl->next_place;
			
		}	
	}
		
		//check the output here
	if(search){
		tmpout = varstart->place_ptr->first_trans_node->output_var;
		
		 if(nodesearch->CaseBlock){
		 	 casebl = nodesearch->CaseBlock->next_n;
		 	 tmpd = casebl->expression_vt->left_value;
		 	 
		 }
		 else if(nodesearch->CondBlock){
		 	if(nodesearch->CondBlock->then_expr_var)
			 	 tmpd = nodesearch->CondBlock->then_expr_var->left_value;
			 else tmpd = nodesearch->CondBlock->then_var;
		 }
		 else if(nodesearch->assign_expr)
		 	tmpd = nodesearch->assign_expr->left_value;
					 	
		 if(!strcmp(tmpout->name,tmpd->name))
			search = true;
		else  search = false;
	}
}
else if(nodesearch && (!nodesearch->CaseBlock && !nodesearch->CondBlock && !nodesearch->assign_expr && !nodesearch->operate_expr))
	search = true;
//if the node proceeding varstart has an operator node, then it must be checked according to the operator type
else if(modn){
	//EDITING HERE
	if(varstart->operator_out){		
		if(varstart->operator_out->op_type == modn->optype){
			for(tmpd = modn->ports_list->first_port;tmpd->next_n!=NULL;tmpd = tmpd->next_n);
			if(!strcmp(varstart->operator_out->output_value->name,tmpd->name))
				search = true;
				value = varstart->operator_out->output_value;
		}
	}
}
else if(equalnode){
	if(varstart->equal_op_out){
		eqtemp = varstart->equal_op_out;
		while(eqtemp){
			if(!strcmp(eqtemp->lhs_value->name,equalnode->left_value->name)){
				search = true;
				break;
			}
			eqtemp = eqtemp->next_equal;
		}
	}
}


return search;

}




//the function first checks if varend is part of a loop i.e the node which generates varend is dependent on varend for its own generation
// if yes, node_list is formed and then Search_back is called again to save the nodes in the loop path.
//then, in the second part,we check if the first non-var node in the path has the same output as varend, if yes, then create it and go to the end of the node_list and attach all the nodes successfuly
//varsearch will return the variable similar to varend in petrigraph loop ,created here
//varstart is the first variable in petrigraph(similar to varend of parse tree) which is the beginning var of the loop(if found, then it exists else varstart is null)
void Create_path_loop(DeclareData *varend, Graph_node *graph_first_node,State_var *first_state,DeclareData*& varsearch,DeclareData *varstart){

int i,num;
Transition_block *transtmp=NULL;
DeclareData *prev_out=NULL,*tmp=NULL,*tmpvar=NULL,*tmpout = NULL,*tmp_check = NULL,*arr_ptr[50];
Place_block *placenode=NULL;
Always_block *tmpalways = NULL;
Assign_var *tmpassign = NULL;
ModuleInstantiate *tmpmod = NULL;
Operate_node *tmpop = NULL;
ComplexOp_node *comp_null = NULL;
Ifthenelse_block *tmpcond =NULL;
Equal_to_op *equaltmp=NULL;
Operate_op *opertmp=NULL;
Compare_operator *compare_tmp = NULL;
struct PathList_struct *first_petrinode = NULL;
bool checknode=false , flag=false,start = false,loop = false;


//DO NOT FIX THE NUMBER OF INDEXES FOR NODE_LIST

if(Search_back_parse_tree(varend,NULL,graph_first_node , num,false , true,false,arr_ptr,50)){
	num=0;
	for(i=0;i<10;i++){
		node_list[i]=new Path_node;
		Initialize_structures(NULL,NULL,NULL,NULL,NULL,node_list[i]);
	}
	i=0;
	//if(varstart)
		//node_list[i++]->varnode =  varstart;          //new DeclareData;
	node_list[i++]->varnode =  varend; 
	
	
	start = Search_back_parse_tree(varend ,NULL, graph_first_node ,i,false,false,false,arr_ptr,50);
	//search for the header node

}


if(start){
	num++;
	first_petrinode = new struct PathList_struct;
	Initialize_array_pointer(first_petrinode);
	do{
//in this part, the node_list is implemented in the petri-net model
		if(node_list[num] && node_list[num]->alnode){
			if(start){
				if(varstart) tmp = varstart;
				else tmp = NULL;
				checknode = true;
				flag = true;
			}
	
			// in this situation, it must be checked if this alnode is already created or not first before creating place - checking in attach_nodes_of_Loop
			if(checknode || !start){
				placenode = new Place_block;
				Initialize_structures(NULL, NULL,placenode,NULL,NULL,NULL);
				//tmp will be obtained from here,for the next loop 
				equaltmp = NULL;opertmp = NULL;
				//only if the loop starts with this node then send varend else not
				if(start)
					attach_nodes_of_Loop(placenode,transtmp,equaltmp,opertmp,node_list[num],graph_first_node,first_state,tmp,start,NULL,tmpout,varend);
				else
					attach_nodes_of_Loop(placenode,transtmp,equaltmp,opertmp,node_list[num],graph_first_node,first_state,tmp,start,NULL,tmpout,NULL);
				//Delete_always_node(graph_first_node,node_list[num]->alnode,true);
				tmp = tmpout;
				//should we delete the always node here itself??
				
				//if(start){
				//	flag = true;
				//	varsearch = tmpout;
				//}
			}
			//checking if the varend is output of an always node--- not needed now
			
		}
		else if(node_list[num] && node_list[num]->assignnode){
			//if its the first time of the loop, then no need to create the input of equaltmp. Let it remain like that and store this node_list[num]
			//if(start) tmp = node_list[num]->assignnode->right_value;
			equaltmp = new Equal_to_op;
			Initialize_structures(NULL, NULL,NULL,NULL,equaltmp,NULL);
			tmpvar = node_list[num]->assignnode->left_value;
			placenode= NULL; opertmp = NULL;
			if(start){
				if(varstart)
					tmp = varstart;
				else tmp = NULL;
				flag = true;
			}
			attach_nodes_of_Loop(placenode,transtmp,equaltmp,opertmp,node_list[num],graph_first_node,first_state,tmp,start,tmpvar,tmpout,NULL);
			//here check if varend is related to this assignnode then dont delete this node
			if(strcmp(varend->name, node_list[num]->assignnode->right_value->name))
				Delete_assign_node(graph_first_node,node_list[num]->assignnode); //CHANGED HERE(COMMENTED)
			tmp = tmpout;
			
			//if(start){
			//	 flag = true;
			//	 varsearch = tmpout;
			//}
			
			/*
			if(start && Search_varassign_list(node_list[num]->assignnode,varend,tmpassign))
				flag = true;
			else	flag=false;*/
		}
		else if(node_list[num] && node_list[num]->modnode){
			if(start){
				//if(!tmp) tmp = node_list[num]->modnode->ports_list->first_port;
				//while(tmp && tmp->next_n){ //CHECKING HERE
					if(varstart)
						tmp = varstart;
					else tmp = NULL;
					checknode = true;
					flag = true;
					//break;
					/*
					if(Search_output_from_node_list(tmp)){
						checknode=true;
						tmp = NULL;
						break;
					}
					else{
						checknode = false;
						break;
					}
					*/
					//tmp = tmp->next_n;
				//}	
			}
			if(checknode || !start){
				opertmp = new Operate_op;
				Initialize_structures(NULL, NULL,NULL,opertmp,NULL,NULL);
				opertmp->op_type = node_list[num]->modnode->optype;
				//from the second iteration of the loop, tmp will be available as output of the previous loop node
				for(prev_out = node_list[num]->modnode->ports_list->first_port;prev_out->next_n!=NULL;prev_out=prev_out->next_n);
				Insert_port_input(node_list[num]->modnode,graph_first_node);
				equaltmp=NULL; placenode = NULL;
				attach_nodes_of_Loop(placenode,transtmp,equaltmp,opertmp,node_list[num],graph_first_node,first_state,tmp,start,prev_out,tmpout,NULL);
				//check if varend is related to this modnode, then dont delete this node
				if(strcmp(varend->name , node_list[num]->modnode->ports_list->first_port->name) && strcmp(varend->name, node_list[num]->modnode->ports_list->first_port->next_n->name))
					Delete_always_node(graph_first_node,tmpalways,false,tmpcond, node_list[num]->modnode,false,tmpop); 
				tmp = tmpout;
				//if(start){
				//	 flag = true;
				//	 varsearch = tmpout;
				//}
			}
			
		}
		else if(node_list[num] && node_list[num]->opnode){
			//tmp = node_list[num]->opnode->input_list->first_port;
			while(tmp){
				Attach_AssignNode_toDFG(tmp,false,graph_first_node,first_state,compare_tmp,false,false);
				if(start) flag = true;
				tmp = tmp->next_n;
			}
			
		}
		else if(node_list[num] && node_list[num]->condnode){
			//tmp = node_list[num]->condnode->if_condition_var;
			Attach_AssignNode_toDFG(tmp,false,graph_first_node,first_state,compare_tmp,false,false);
			if(start) flag = true;
			
		}
	   	
		
		//flag will become true in the first run of this loop
		if(flag){
			//num=10;
			start=false;
			flag = false;
			if(placenode && !varstart) first_petrinode->placenode = placenode;
			else if(transtmp && !varstart) first_petrinode->trannode = transtmp;
			else if(equaltmp && !varstart) first_petrinode->eqnode = equaltmp;
			else if(opertmp && !varstart) first_petrinode->opnode = opertmp;
			else if(compare_tmp && !varstart) first_petrinode->compnode = compare_tmp;
		}	
		num++;
		//else	num--;
	}while(num<10 && strcmp(varend->name,tmpout->name));		
			
		//finally, first_node should be attached to its previous node. 
		if(varstart)
			varsearch = varstart;
		else{
			Attach_first_node_in_Loop(tmp,first_petrinode);
			varsearch = tmpout;
		}
		delete first_petrinode;
		first_petrinode = NULL;
		
}

if(!flag){
	//delete the node_lsit and keep it free
	Delete_node_list();
}


//return flag;

}

//function to attach theloop nodes, when the loop is in process of creation.
//here endvar brings the value of the output of the previous node generated(input for this new node) and tmpsend gets the value of the output of newly created node here.
//invar is the variable to indicate the inputvar of the CaseBlock if alnode contains a CaseBlock(from parse tree)
void attach_nodes_of_Loop(Place_block*& place_new,Transition_block*& trans,Equal_to_op*& equal_new,Operate_op*& op_new,Path_node *node,Graph_node *graph_first_node,State_var *first_state,DeclareData*& endvar,bool startflag,DeclareData *opoutput,DeclareData*& tmpsend,DeclareData *invar){


Transition_block *prevtr=NULL;
Always_block *tmpal = NULL;
ModuleInstantiate *tmpm =  NULL;
Operate_node *opernull = NULL;
DeclareData *var=NULL,*prev_var=NULL, *tmp=NULL;
Place_block *pl_null=NULL;
Ifthenelse_block *tmpnull = NULL , *tmpnull_tmp = NULL;
bool search = false , flag = false, loopcreate = false,checkflag = false;


if(place_new){
	//check first if this alnode has been  built as clocked place node
	//trans is just used here
	if(node->alnode->assign_expr && Search_node_from_clocked_transition(node->alnode,trans)){
		delete place_new;place_new=NULL;
		if(endvar) endvar->transition_out = trans;
		search = true;
	}
	if(!search){
		
		if(node->alnode->CaseBlock || node->alnode->CondBlock || node->alnode->assign_expr){
			//send the particular condexpr in alnode->CondBlock which must be implemented only.
			if(node->condnode) tmpnull = node->condnode;
			if(endvar)
				attach_transition_nodes(place_new,false,node->alnode,graph_first_node,first_state,false,endvar,tmpnull,true,NULL);
		
			else attach_transition_nodes(place_new,false,node->alnode,graph_first_node,first_state,false,NULL,tmpnull,true,invar);
			
			
			tmpsend = place_new->first_trans_node->output_var;
		
			if(endvar && node->alnode->CaseBlock)
				Delete_case_node(node->alnode,endvar,graph_first_node,tmpnull_tmp);
			else if(endvar && node->alnode->CondBlock)
				Delete_case_node(node->alnode,endvar,graph_first_node,tmpnull);
			//TO BE CHECKED HERE(CHANGED HERE)
			else if(!node->alnode->CaseBlock && !node->alnode->CondBlock)
				Delete_always_node(graph_first_node,node->alnode,true,tmpnull,tmpm,false,opernull);
		}
		if(endvar){
			if(!endvar->place_ptr) endvar->place_ptr = place_new;
			else Insert_place_in_list(endvar,place_new);
		}
		
		//insert the other place inputs if available TOBE DONE
	}
	else if(search && node->alnode->assign_expr){
		tmpsend = trans->output_var;
		
	}
	
}
else{
	if(op_new && node->modnode){
		for(tmp = node->modnode->ports_list->first_port; tmp!=NULL;tmp=tmp->next_n){
			if(tmp->data_type == integer){
				op_new->op2 = new DeclareData;
				assign_value(op_new->op2,tmp);
				break;
			}
		}
		//other input of modnode apart from the endvar
		for(tmp = node->modnode->ports_list->first_port; tmp->next_n!=NULL;tmp=tmp->next_n){
			//check if the modnode has already been created
			if(Search_OutputVarFrom_Places(tmp,first_place_node,prevtr,pl_null,NULL,prev_var,graph_first_node,first_state,false,loopcreate,true)){
				if((prev_var && Search_node_Loop(NULL,prev_var,node->modnode,NULL,var)) || (prevtr && Search_node_Loop(NULL,prevtr->output_var,node->modnode,NULL,var))){
					checkflag = true;
					break;	
				}	
			}
			if(strcmp(tmp->name,endvar->name) && tmp->data_type!=integer){
				if(!tmp->next_n->next_n){
					flag = true;
					break;
				}
			}
			else flag = false;
		}
		if(checkflag){
			//delete the op_new since its already created
			if(op_new->op2) Delete_var_node(op_new->op2);
			delete op_new ; op_new = NULL;
			tmpsend = var;
		}
		else if(/*!startflag &&*/ endvar){
			//this means endvar is already created
			if(!op_new->op1) op_new->op1 = endvar;
			else if(!op_new->op2) op_new->op2 = endvar;
			op_new->op_type = node->modnode->optype; //operator  type
			endvar->operator_out = op_new;
			op_new->output_value = new DeclareData;
			assign_value(op_new->output_value,opoutput);
			//this is for checking the other input of the modnode which is not endvar(tmp)
			
			if(flag){
				if(Search_OutputVarFrom_Places(tmp,first_place_node,prevtr,pl_null,NULL,prev_var,graph_first_node,first_state,false,loopcreate,true)){
					if(prevtr){
						var = prevtr->output_var;
						if(!prevtr->output_var->operator_out) prevtr->output_var->operator_out = op_new;
						else insert_in_operator_list(prevtr->output_var,op_new,NULL,true,NULL,false);
					}
					else if(prev_var){
						var = prev_var;
						if(!prev_var->operator_out) prev_var->operator_out = op_new;
						else insert_in_operator_list(prev_var,op_new,NULL,true,NULL,false);
					}
					
					if(!op_new->op1) op_new->op1 = var;
					else if(!op_new->op2) op_new->op2 = var;
				}
				//for now, we are not attaching the other input if in case it cannot be searched above.
				else{
					if(op_new->op1){
						op_new->op2= new DeclareData;
						assign_value(op_new->op2,tmp);
						op_new->op2->operator_out = op_new;
						varinput_list[list_num++] = op_new->op2;
					}
					else{
						op_new->op1 = new DeclareData;
						assign_value(op_new->op1,tmp);
						op_new->op1->operator_out = op_new;
						varinput_list[list_num++] = op_new->op1;
					}
				}
			}
				
			tmpsend = op_new->output_value; //send the output
			
		}
		else{
			//this means endvar is not created,and is just obtained as the output of the previous node in analysis_parse graph, which will be attached later. now dont attach the endvar
			op_new->output_value = new DeclareData;
			assign_value(op_new->output_value,opoutput);
			op_new->op_type = node->modnode->optype; //operator type
			
			endvar->operator_out = op_new;
			tmpsend = op_new->output_value; //send theoutput thru endvar only
			//for the other input of modnode
			if(flag){
				if(tmp && Search_OutputVarFrom_Places(tmp,first_place_node,prevtr,pl_null,NULL,prev_var,graph_first_node,first_state,false,loopcreate,true)){
					if(prevtr){
						op_new->op2 = prevtr->output_var;
						if(!prevtr->output_var->operator_out) prevtr->output_var->operator_out = op_new;
						else insert_in_operator_list(prevtr->output_var,op_new,NULL,true,NULL,false);
					}
					else if(prev_var){
						op_new->op2 = prev_var;
						if(!prev_var->operator_out) prev_var->operator_out = op_new;
						insert_in_operator_list(prev_var,op_new,NULL,true,NULL,false);
					}
				}
				// putting the other input if its not found at this stage
				else{
					if(op_new->op1){
						op_new->op2= new DeclareData;
						assign_value(op_new->op2,tmp);
						op_new->op2->operator_out = op_new;
						varinput_list[list_num++] = op_new->op2;
					}
					else{
						op_new->op1 = new DeclareData;
						assign_value(op_new->op1,tmp);
						op_new->op1->operator_out = op_new;
						varinput_list[list_num++] = op_new->op1;
					}
				}
				
			}
			//only if the other input is an integer, then insert it
			else if(tmp->data_type == integer){
				if(!op_new->op2){
					op_new->op2 = new DeclareData;
					assign_value(op_new->op2, tmp);
				}
				else if(!op_new->op1){
					op_new->op1 = new DeclareData;
					assign_value(op_new->op1,tmp);
				}
			}
			
		}
		//Delete_always_node(graph_first_node,tmpal,false,tmpnull, node->modnode,false); //CHANGED HERE(COMMENTED)
		
	}
	else if(node->assignnode){
		equal_new->opsymbol = '=';
		
		if(  endvar){
			equal_new->rhs_value = endvar;
			if(!endvar->equal_op_out) endvar->equal_op_out = equal_new;
			else Insert_in_equalto_list(NULL,endvar,equal_new);
			equal_new->lhs_value = new DeclareData;
			assign_value(equal_new->lhs_value,opoutput);
			tmpsend = equal_new->lhs_value; //send the output
		}
		else{
			// no need for putting the input to equal_new here
			equal_new->lhs_value = new DeclareData;
			assign_value(equal_new->lhs_value,opoutput);
			tmpsend = equal_new->lhs_value; //send the output
		}
	}
	
}


}


//fn to search if alnode is already existing as clocked transition
bool Search_node_from_clocked_transition(Always_block *alnode, Transition_block*& tran){

Transition_block *tmp = NULL;
DeclareData *tmpvar = NULL;
bool search=false;


tmp = first_place_node->first_trans_node;


while(tmp){

	tmpvar = alnode->assign_expr->left_value;
	if(!strcmp(tmp->data_node->assignment_graph->lhs_value->name, tmpvar->name)){
		tran = tmp;
		search = true;
		break;
	}
	tmp = tmp->next_trans_node;

}


return search;

}






//fn to search if varsearch is output from any of the nodes in node_list
bool Search_output_from_node_list(DeclareData *varsearch ){

DeclareData *tmp = NULL;
Always_block *tmpal = NULL;
Assign_var *tmpassign = NULL;
ModuleInstantiate *tmpmod = NULL;
Operate_node *tmpop = NULL;
ComplexOp_node *comp_null = NULL;
Ifthenelse_block *tmpcond =NULL;
int i=0;

bool search = false;

while(node_list[i] && i<=10){
	if(node_list[i]->alnode && Search_Always_list(node_list[i]->alnode , varsearch , tmpal)){
		search = true;
		break;
	}
	else if(node_list[i]->opnode && Search_operation_list(node_list[i]->opnode , varsearch,tmpop,NULL,comp_null)){
		search = true;
		break;
	}
	else if(node_list[i]->assignnode && Search_varassign_list(node_list[i]->assignnode , varsearch,tmpassign)){
		search = true;
		break;
	}
	else if(node_list[i]->condnode && Search_ifthenelse_list(node_list[i]->condnode , varsearch,tmpcond)){
		search=true;
		break;
	}
	else if(node_list[i]->modnode && Search_ModuleInst_list(node_list[i]->modnode , varsearch,tmpmod)){
		search=true;
		break;
	}
	i++;
}

return search;
}

//function to search the parse tree for the node which generated varend
//flag is coming externally from Create_loop_path
//if flag is false, then the fn is called externally, else its called internally
//check_path is true if your r using the function for just checking the path if its a loop or not, false if you are using it to create the loop path n save in node_list
bool Search_back_parse_tree(DeclareData *varend,DeclareData *tmpvar,Graph_node *graph_first_node , int &num,bool flag,bool check_path,bool start,DeclareData** arr_ptr, int arr_size){

ModuleInstantiate *tmpmod=NULL;
Always_block *tmpal=NULL;
Assign_var *tmpassign=NULL;
DeclareData *tmp= NULL,*tmpnode=NULL,*tmpcheck = NULL;
Operate_node *tmpop=NULL;
ComplexOp_node *tmpcomp=NULL;
Ifthenelse_block *tmpcond = NULL,*condexpr = NULL;
bool node=false , assign = false,search_dominator = true,cflag = false;
int i;

if(!flag) tmp = varend;
else tmp = tmpvar;

node = false;

if(!flag)
	Initialize_array(arr_ptr,arr_size);
	
else if(Check_node_from_array(arr_ptr,arr_size,tmp)){
	node = false;
	search_dominator = false;
}

	//node=false;
if(start && search_dominator && ((tmp==varend) || !strcmp(tmp->name, varend->name))){
	node=true;
		//node_list[num++]->varnode = tmp;
}
start=true;
if(!node && search_dominator){
	if(flag) Change_node_in_array(arr_ptr,arr_size,tmp,true); 
	
	if(!node && graph_first_node->module_inst_node){
		if(Search_ModuleInst_list(graph_first_node->module_inst_node,tmp,tmpmod)){
			//node = true;
			
			tmpnode = tmpmod->ports_list->first_port;
			//should not traverse the output port
			while(tmpnode && tmpnode->next_n && tmpnode->data_type!=integer){
				if( Search_back_parse_tree(varend,tmpnode,graph_first_node,num,true,check_path,start,arr_ptr,arr_size)){
					if(!check_path) node_list[num++]->modnode = tmpmod;
					node=true;
					break;
				}
				 tmpnode=  tmpnode->next_n;
			}
		}
		else node=false;
	}
	if(!node && graph_first_node->always_node){
		if(Search_Always_list(graph_first_node->always_node,tmp,tmpal)){
			i=num;
			
			if(tmpal->event_controls){
				tmpnode = tmpal->event_controls->first_port;
				if(tmpal->CondBlock)
					tmpcheck = tmpal->CondBlock->then_expr_var->right_value;
				else if(tmpal->CaseBlock)
					cflag = true;
			}
			else if(tmpal->assign_expr){
				 tmpnode = tmpal->assign_expr->right_value;
				 tmpcheck = tmpnode;
				 assign = true;
			}
			while(tmpnode){
			//EDITED HERE CHANGED!!
				condexpr = tmpal->CondBlock;
				while(condexpr){
					if(condexpr->then_expr_var && !strcmp(tmpnode->name,condexpr->then_expr_var->right_value->name)){
						tmpcheck = condexpr->then_expr_var->right_value;
						break;
					}
					condexpr = condexpr->else_expr_block;
				}
				if(cflag || (tmpcheck && !strcmp(tmpnode->name,tmpcheck->name) && tmpnode->data_type!=integer)){				
					if(Search_back_parse_tree(varend,tmpnode , graph_first_node,num,true,check_path,start,arr_ptr,arr_size)){
						node=true;
						if(!check_path) node_list[num++]->alnode = tmpal;
						if(!cflag && !assign && tmpal->CondBlock->else_expr_block && condexpr && !check_path) node_list[num-1]->condnode = condexpr;
						//else if(cflag) node_list[i]->casenode
						break;
					}
				}
				tmpnode = tmpnode->next_n;
			}
			
		}
		else node=false;
	}
	if(!node && graph_first_node->varassign_node){
		if(Search_varassign_list(graph_first_node->varassign_node , tmp,tmpassign)){
			//node=true;
			
			tmpnode = tmpassign->right_value;
			if(Search_back_parse_tree(varend,tmpnode,graph_first_node,num,true,check_path,start,arr_ptr,arr_size)){
				node = true;
				if(!check_path) node_list[num++]->assignnode = tmpassign;
			}
		}
		else node=false;
	}
	if(!node && graph_first_node->operation_node){
		if(Search_operation_list(graph_first_node->operation_node , tmp,tmpop,NULL,tmpcomp)){
			//node=true;
			
			tmpnode = tmpop->input_list->first_port;
			while(tmpnode){
				if(Search_back_parse_tree(varend,tmpnode , graph_first_node,num,true,check_path,start,arr_ptr,arr_size)){
					node=true;
					if(!check_path) node_list[num++]->opnode = tmpop;
					break;
				}
				
				tmpnode = tmpnode->next_n;
			}
			
		}
		else node=false;
	}
	if(!node && graph_first_node->ifthenelse_node){
		if(Search_ifthenelse_list(graph_first_node->ifthenelse_node,tmp,tmpcond)){
			//node=true;
			
			tmpnode = tmpcond->if_condition_var;
			if(Search_back_parse_tree(varend,tmpnode,graph_first_node,num,true,check_path,start,arr_ptr,arr_size)){
				node = true;
				if(!check_path) node_list[num++]->condnode = tmpcond;
			}
		}
		else node=false;
	}
		
} //end of if

return node;

}

bool Search_ifthenelse_list(Ifthenelse_block *condnode , DeclareData *var , Ifthenelse_block*& tmpcond){

Ifthenelse_block *tmp=NULL;
Ifthenelse_block *tmpc=NULL;
bool flag=false;
tmp = condnode;
while(tmp){
	tmpc = tmp;
	while(tmpc){
		if((tmpc->then_var && !strcmp(var->name , tmpc->then_var->name)) || (tmpc->then_expr_var && !strcmp(var->name , tmpc->then_expr_var->left_value->name))){
			flag=true;
			tmpcond = tmpc;
			break;
		}
		tmpc = tmpc->else_expr_block;
	}
	if(flag) break;
	else tmp = tmp->next_block;

}

return flag;

}

//function to search the output of an operation node 
bool Search_operation_list(Operate_node *opnode , DeclareData *var,Operate_node*& tmpop , ComplexOp_node *compnode , ComplexOp_node*& tmpcomp){

Operate_node *tmp=NULL;
ComplexOp_node *tmpc = NULL;
bool flag=false;

tmp = opnode;
while(tmp){
	if(!strcmp(var->name , tmp->output->name)){
		flag= true;
		tmpop = tmp;
		break;
	}
	tmp = tmp->next_op;

}
tmpc = compnode;
while(tmpc){
	if(!strcmp(var->name , tmpc->out_value->name)){
		flag=true;
		tmpcomp = tmpc;
		break;
	}
}

return flag;

}

bool Search_varassign_list(Assign_var *assign , DeclareData *var , Assign_var*& tmpassign ){

Assign_var *tmp=NULL;

bool flag=false;
tmp = assign;
while(tmp){
	if(!strcmp(var->name , tmp->left_value->name)){
		tmpassign = tmp;
		flag=true;
		break;
	}
	tmp = tmp->next_n;
}


return flag;
}

bool Search_Always_list(Always_block *alnode ,DeclareData *var,Always_block*& tmpal){

Always_block *tmp=NULL;
bool flag=false;
Ifthenelse_block *tmpcond=NULL;
Case_Statement *tmpcase=NULL;
tmp = alnode;

while(tmp){
	if(tmp->assign_expr){
		if(!strcmp(var->name , tmp->assign_expr->left_value->name)){
			flag=true;
			tmpal = tmp;
			break;
		}
	}
	else if(tmp->operate_expr){
		if(!strcmp(var->name , tmp->operate_expr->output->name)){
			flag=true;
			tmpal=tmp;
			break;
		}
	}
	else if(tmp->comp_expr){
		if(!strcmp(var->name,tmp->comp_expr->out_value->name)){
			flag=true;
			tmpal=tmp;
			break;
		}
	}
	else if(tmp->CondBlock){
		tmpcond = tmp->CondBlock;
		while(tmpcond){
			if((tmpcond->then_expr_var && !strcmp(var->name , tmpcond->then_expr_var->left_value->name))|| (tmpcond->then_var && !strcmp(var->name , tmpcond->then_var->name))){
				
				flag=true;
				tmpal = tmp;
				break;
			}
			tmpcond = tmpcond->else_expr_block;
		}
		if(flag) break;		
	}
	else if(tmp->CaseBlock){
		tmpcase = tmp->CaseBlock;
		while(tmpcase){
			if(tmpcase->expression_vt && !strcmp(var->name ,tmpcase->expression_vt->left_value->name)){
				flag = true;
				tmpal = tmp;
				break;
			}
			tmpcase = tmpcase->next_n;
		}
		if(flag) break;
	}
	//else tmp=NULL;
	
	if(!flag) tmp = tmp->next_n;
	else tmp =NULL;
	
}
return flag;

}
	

//function to search the module instantiion list for a module's output
bool Search_ModuleInst_list( ModuleInstantiate *modnode,DeclareData *var,ModuleInstantiate*& tmpm){

ModuleInstantiate *tmp=NULL;
DeclareData *tmpd=NULL;
bool flag=false;

tmp=modnode;
while(tmp){
	for(tmpd = tmp->ports_list->first_port ; tmpd->next_n!=NULL;tmpd=tmpd->next_n);
	if( !strcmp(var->name , tmpd->name)){
		flag=true;
		tmpm = tmp;
		break;
	}
	 tmp = tmp->nextm;
}

return flag;
}

//function to search if a variable is output_var from already created place nodes
// the outputvar of the prev dfg node(prev_out) is being passed for attaching the assign node or operate nodes
//tran_node is returned only when the output_var to be searched is from a transition node
//var is the variable to be searched
//loopcheck is a flag to indicate that the function is being called,when a loop creation is in process. if loopcheck is true,that means its called when loop is not being created. if false, that means the fn is called,when loop is being created,and it should not check for loops
//search_depth is to indicate if here, the loop was created
//extflag is to indicate if the function is called from inside or externally it is false when called internally. true when called externally
bool Search_OutputVarFrom_Places( DeclareData *var , Place_block *place_n , Transition_block*& tran_node , Place_block*& new_place , DFG_block *dfg_node , DeclareData*& prev_out,Graph_node *graph_first_node,State_var *first_state,bool loopcheck,bool& search_depth,bool extflag){

Transition_block *tmp_tr = NULL;
bool search = false , node_down = false;
State_var *tmpstate = NULL;
Place_block *tmp_place = NULL , *place_temp = NULL;
DeclareData *outvar_s = NULL , *outvar= NULL ,*var_ret = NULL , *tmp = NULL , *tmpvar=NULL , *var_list[10] , *arr_ptr[50] , *var_ptr[100];
Operate_op *opnext=NULL , *opnext_s=NULL , *operate_s=NULL;
Equal_to_op *node=NULL;
Signal_selector *signal_tmp = NULL;
Compare_operator *compare_tmp = NULL;
struct PathList_struct *loop_node = NULL;
struct BasicBlock_Struct *block_ret = NULL;
int i =0 , num = 0;


if(loopcheck && Search_back_parse_tree(var,NULL,graph_first_node , num,false,true,false,arr_ptr,50)){
	//now loop exists in parse_tree following var. now check if the loop is already created or not
	//tmpvar = var;
	//since var is from Parsetree, the var must be searched normally in petrigraph to get its similar node in petri graph.
	//CHANGED HERE TOO  LAST VAR
	if(Search_OutputVarFrom_Places(var,place_n,tran_node ,new_place,dfg_node , prev_out,graph_first_node,first_state,false,search_depth,true)){
		//now search if the var is associated with a loop or not.
		if(prev_out) tmpvar = prev_out;
		else if(tran_node) tmpvar = tran_node->output_var;
		
		if(prev_out && Search_back_petri_model(prev_out,NULL,true,true,first_state,i,false,loop_node,false,var_list,10,false,block_ret,true,prev_out))
			search = true;
		else if(tran_node && Search_back_petri_model(tran_node->output_var,NULL,true,true,first_state,i,false,loop_node,false,var_list,10,false,block_ret,true,tran_node->output_var))
			search = true;
		else if((prev_out && tmpvar!=prev_out) || (tran_node && tmpvar!=tran_node->output_var))
			search = true;
		
		else{
			if(prev_out)
				Create_path_loop(var, graph_first_node,first_state,var_ret,prev_out);
			else if(tran_node)
				Create_path_loop(var, graph_first_node,first_state,var_ret,tran_node->output_var);
			search = true;
			prev_out = var_ret;
			tran_node = NULL;
			//find that var in this created loop
			search_depth = true;
		}
	}
	else{
		Create_path_loop(var, graph_first_node,first_state,var_ret,NULL);
		search = true;
		prev_out = var_ret;
		tran_node = NULL;
		//find that var in this created loop
		search_depth = true;
	}
	//else search = false;
	
}

//if the place is a parallel place node and the fn is called when loop creation is not going on
while(!search && place_n){
	if(!search /*&& place_n->next_trans_node*/){
	for( tmp_tr = place_n->first_trans_node ; search!=true && tmp_tr!=NULL;tmp_tr = tmp_tr->next_trans_node){
		if(var->name == tmp_tr->output_var->name)
			{ if(tmp_tr->output_var->place_ptr && new_place)
				{delete new_place; new_place=NULL; new_place = tmp_tr->output_var->place_ptr;}
			
			search = true;
			tran_node = tmp_tr;
			break;
			}
		else if(tmp_tr->outgoing_external_place){
			if( Search_OutputVarFrom_Places( var , tmp_tr->outgoing_external_place , tran_node ,new_place,dfg_node , prev_out,graph_first_node,first_state,loopcheck,search_depth,false)){
				search = true;
				break;
			}
		}
		//search for the equal,operate,place attached to output_var
		outvar = tmp_tr->output_var ;
		//EDITING HERE FINAL!
		//CHANGE 1
		if(Search_depth_OutputVarFrom_Places(outvar,var,graph_first_node,first_state,loopcheck,search_depth,prev_out,tran_node,new_place,dfg_node,true,true,var_ptr)){
			search = true;
			break;
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
	else if( place_n->first_trans_node->outgoing_external_place){
	//	if(!search_depth) loopcheck = true;
		//else if(search_depth) loopcheck = false;
		
		if(Search_OutputVarFrom_Places( var , place_n->first_trans_node->outgoing_external_place, tran_node , new_place,NULL,prev_out,graph_first_node,first_state,loopcheck,search_depth,false))
			search = true;
	}

}
	place_n = place_n->next_place; //for parallel places
}

//searching from thestates . this part is active only if the extflag is true(being called from outside)
if(!search && extflag && first_state && !Search_var_InStateList(var,first_state)){
	
	tmpstate = first_state;
	while(tmpstate){
		tmp = tmpstate->state_name;
		//CHANGED HERE
		if(tmp->place_ptr){
			place_temp = tmp->place_ptr;
			while(place_temp){
				if(Search_OutputVarFrom_Places( var , place_temp, tran_node , new_place,NULL,prev_out,graph_first_node,first_state,false,search_depth,false)){
					search = true;
					break;
				}
				place_temp = place_temp->next_place;
			}
			if(search) break;
		}
		if(!search && tmp->comparator_out){
			compare_tmp = tmp->comparator_out;
			while(compare_tmp){
				if(Search_depth_OutputVarFrom_Places(compare_tmp->value_out,var,graph_first_node,first_state,loopcheck,search_depth,prev_out,tran_node,new_place,dfg_node,false , true,var_ptr)){
					search = true;
					break;
				}
				compare_tmp = compare_tmp->next_comparator;
			}
			if(search) break;
		}
		if(!search && tmp->signal_selector_out){
			//put loop
			signal_tmp = tmp->signal_selector_out;
			while(signal_tmp){
				if(Search_depth_OutputVarFrom_Places(signal_tmp->out_signal,var,graph_first_node,first_state,loopcheck,search_depth,prev_out,tran_node,new_place,dfg_node,false,true,var_ptr)){
					search = true;
					break;
				}
				signal_tmp = signal_tmp->next_selector;
			}
			if(search) break;
		}
		tmpstate = tmpstate->next_state;
	}	
}

//if no place, then its ordered to search from dfg_node
if(!search && dfg_node && dfg_node->output){
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
		
	}
}
else{
	//search all the outputs of the parallel equalto nodes first
	if(!search && Search_in_equalto_list(var, tmpvar)){
		prev_out = tmpvar;
		search = true;
		//break;
	}
	//then search depth search wise the output of every equalto node
	//CHANGED HERE!
	node = first_EqualTo_node;
	while(!search && extflag && node){
		tmpvar = node->lhs_value;
		if(Search_depth_OutputVarFrom_Places(tmpvar,var,graph_first_node,first_state,loopcheck,search_depth,prev_out,tran_node,new_place,dfg_node,false,true,var_ptr)){
			search = true;
			break;
		}
	
		node = node->next_equal;
	}
	
}


return search;
}

//extension of above function
// this function will have a flag called 
//if fn called from outside, startflag is true else startflag is false
bool Search_depth_OutputVarFrom_Places(DeclareData *outvar,DeclareData *var,Graph_node *graph_first_node,State_var *first_state,bool loopcheck,bool search_depth,DeclareData*& prev_out,Transition_block*& tran_node,Place_block *new_place,DFG_block *dfg_node, bool searchflag,bool startflag, DeclareData** arr_ptr){


bool node_down = false , loop_start = true , search = false;
Place_block *place = NULL;
Equal_to_op *tmpeq = NULL;
Signal_selector *tmp_sig = NULL;
Compare_operator *tmp_comp = NULL;

if(startflag){
	startflag = false;
	Initialize_array(arr_ptr,100);
}
else if(Check_node_from_array(arr_ptr,100,outvar))
	loop_start = false;


			while(loop_start && outvar){
				Change_node_in_array(arr_ptr,100,outvar,true); //insert here
				node_down = false;
				if(!strcmp(var->name,outvar->name)){
					search = true;
					prev_out = outvar;
					break;
				}
				if(!node_down && searchflag && outvar->place_ptr){
					node_down = true;
					place = outvar->place_ptr;
					while(place){
						if(Search_depth_OutputVarFrom_Places(place->first_trans_node->output_var,var,graph_first_node,first_state,loopcheck,search_depth,prev_out,tran_node,new_place,dfg_node,searchflag,false,arr_ptr)){
							search = true;
							break;
						}
					//CHANGED HERE
					/*
					else if(Search_OutputVarFrom_Places(var,outvar->place_ptr,tran_node,new_place,dfg_node,prev_out,graph_first_node,first_state,loopcheck,search_depth,false)){
					
						search=true;
						break;
					}
					*/
						else node_down = false;
						place = place->next_place;
					}
					if(search) break;
					
				}
				
				 if(!node_down && outvar->equal_op_out){
					node_down = true;
					tmpeq = outvar->equal_op_out;
					while(tmpeq){
						outvar = tmpeq->lhs_value; //end of while loop	
							
					//if(outvar->place_ptr)
					//	continue;
						 if(Search_depth_OutputVarFrom_Places(outvar,var,graph_first_node,first_state,loopcheck,search_depth,prev_out,tran_node,new_place,dfg_node,searchflag,false,arr_ptr)){
							search = true;
							break;
						}
						else node_down = false;
						tmpeq = tmpeq->next_equal;
					}
					if(search) break;
				}
				if(!node_down && outvar->operator_out){
					node_down = true;
					outvar = outvar->operator_out->output_value;
					
					if(outvar->place_ptr)
						continue;
					else if(Search_depth_OutputVarFrom_Places(outvar,var,graph_first_node,first_state,loopcheck,search_depth,prev_out,tran_node,new_place,dfg_node,searchflag,false,arr_ptr)){
						search = true;
						break;
					}
					else node_down = false;
				}
				 if(!node_down && outvar->comparator_out){
					node_down = true;
					tmp_comp = outvar->comparator_out;
					while(tmp_comp){
						outvar = tmp_comp->value_out;
						if(Search_depth_OutputVarFrom_Places(outvar,var,graph_first_node,first_state,loopcheck,search_depth,prev_out,tran_node,new_place,dfg_node,searchflag,false,arr_ptr)){
							search = true;
							break;
						}
						else node_down = false;
						tmp_comp = tmp_comp->next_comparator;
					}
					if(search) break;
				}
				if(!node_down && outvar->signal_selector_out){
					node_down = true;	
					tmp_sig = outvar->signal_selector_out;
					while(tmp_sig){
						 outvar = tmp_sig->out_signal;
						 if(Search_depth_OutputVarFrom_Places(outvar,var,graph_first_node,first_state,loopcheck,search_depth,prev_out,tran_node,new_place,dfg_node,searchflag,false,arr_ptr)){
						 	search = true;
						 	break;
						 }
						 else node_down = false;
						 tmp_sig = tmp_sig->next_selector;				 
					}
					if(search) break;
				}
				if(!node_down && outvar->dfgnode_out){
					node_down = true;
					
					outvar = outvar->dfgnode_out->output;
					if(outvar->place_ptr)
						continue;
					else if(Search_depth_OutputVarFrom_Places(outvar,var,graph_first_node,first_state,loopcheck,search_depth,prev_out,tran_node,new_place,dfg_node,searchflag,false,arr_ptr)){
						search = true;
						break;
					}
					else node_down = false;
				}
				
				if(!node_down) outvar = NULL;
			}//end of while

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


//to search a variable in the equalto list for parallel assign nodes
bool Search_in_equalto_list( DeclareData *searchvar ,DeclareData*& prev_var ){

Equal_to_op *tmp=NULL;
bool flag=false;

tmp = first_EqualTo_node;
while(tmp){
	if(!strcmp(searchvar->name , tmp->lhs_value->name)){
		prev_var = tmp->lhs_value;
		flag=true;
		break;
	}
	else 
	tmp = tmp->next_equal;
}


return flag;

}





//function to create DFG from functional unit modules
void Create_DFG_from_FU( Graph_node *gnode , DFG_block *dfg_node , Place_block *plnode , ModuleInstantiate *modnode,Graph_node *graph_first_node , State_var *first_state){

DeclareData *dnode1 =NULL;
DeclareData *dnode2 =NULL;
DeclareData *prev_outvar =NULL , *condvar = NULL;
DFG_block *dfg_search = NULL;
Place_block *newplace=NULL;
Place_block *newplace1=NULL;
DeclareData *output=NULL;
Condition_block *conditional_node = NULL;
Transition_block *prevtr = NULL; 
Case_Statement *case_expr = NULL;
bool loop_create = false;
//previous transition node whose output var is one of the input variables to the FU
//dnode1 is the variable in the moduleInstantiate ports list
//dnode2 is the variable in the FU module node input ports list
// its needed to change the name of dnode2 to that of dnode1 in order to search for the variables in the previous place nodes

if(gnode->operation_node){
	Operate_op *operate_n = new Operate_op;
	Initialize_structures(NULL, NULL,NULL,operate_n,NULL,NULL);
	dfg_node->operation_graph = operate_n;
	//first attach the output here
	for(dnode1=modnode->ports_list->first_port;dnode1->next_n!=NULL;dnode1 = dnode1->next_n);
	operate_n->output_value = new DeclareData;
	assign_value(operate_n->output_value,dnode1);
	gnode->operation_node->output->name = dnode1->name ; 
	

	for( dnode1=modnode->ports_list->first_port ; dnode1->next_n!=NULL; dnode1=dnode1->next_n){
	
		prevtr=NULL;prev_outvar=NULL;
		if(dnode1->data_type!=integer && (Search_OutputVarFrom_Places( dnode1 , first_place_node , prevtr ,  newplace/*null*/ , dfg_search , prev_outvar,graph_first_node,first_state,true,loop_create,true)||Search_OutputVarFrom_Places(dnode1,first_parallel_place,prevtr,newplace,dfg_search,prev_outvar,graph_first_node,first_state,true,loop_create,true)) || (Search_output_from_node_list(dnode1))){
	
		/*	if(dnode1->prev_n){
						
				 newplace = Search_place_of_input(first_state,true,NULL,dnode1->prev_n,output); //previous input's place
				 if(newplace){
							//state_place_input is the list of state signals in newplace, placenode of the previous input
					newplace1 = Search_place_of_input(first_state,true,NULL, dnode1,output); //second input's place
					if(newplace1 && Check_state_of_input(newplace,newplace1)){
						if(dnode1== modnode->ports_list->first_port) operate_n->op1 = output;
						else operate_n->op2 = output;
					}
					
				}
			}*/
				if(prevtr){
				prevtr->outgoing_external_dfg = dfg_node;
				prevtr->output_var->operator_out = operate_n;
				if(dnode1== modnode->ports_list->first_port)
					operate_n->op1 = prevtr->output_var;
				else operate_n->op2= prevtr->output_var;
				
				}
				else if( prev_outvar){
				prev_outvar->operator_out = operate_n;
				//prev_outvar->dfgnode_out = dfg_node;
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
		else{
			//search in the equalto list
			if(Search_in_equalto_list(dnode1 , prev_outvar)){
				if(dnode1== modnode->ports_list->first_port)
					operate_n->op1 = prev_outvar;
				else	operate_n->op2 = prev_outvar;
			}
		}
	
	
	}
	
	Select_from_operator_list ( operate_n ,NULL,gnode->operation_node->operator_type);
	dfg_node->output = operate_n->output_value;
	/*
	if(dnode1->next_n==NULL){
		gnode->operation_node->output->name = dnode1->name ; 
		operate_n->output_value = new DeclareData;
		Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,operate_n->output_value,NULL,NULL,NULL);
		operate_n->output_value->name = gnode->operation_node->output->name;
		
	}*/
	
	// if the graph node contains another  operation as well
	//to be done later
	
}
else if(gnode->always_node){
	//this is the case for decoder. the always_node contains a CaseBlock. the structure should be converted to case wise. if(condition_var == case_value) then expression_ct->left_value = 1
	if(gnode->always_node->CaseBlock){
		if(Search_OutputVarFrom_Places( gnode->always_node->CaseBlock->condition_var , first_place_node , prevtr ,  newplace/*null*/ , dfg_search , prev_outvar,graph_first_node,first_state,true,loop_create,true)||Search_OutputVarFrom_Places(gnode->always_node->CaseBlock->condition_var ,first_parallel_place,prevtr,newplace,dfg_search,prev_outvar,graph_first_node,first_state,true,loop_create,true)){
			if(prevtr)
				condvar = prevtr->output_var;
			else condvar = prev_outvar;
		}
		
		
		case_expr = gnode->always_node->CaseBlock->next_n;
		while(case_expr){
			conditional_node = new Condition_block;
			Initialize_structures(conditional_node , NULL,NULL,NULL,NULL,NULL);
			conditional_node->equal_cond = new Equal_to_op;
			Initialize_structures(NULL, NULL,NULL,NULL,conditional_node->equal_cond,NULL);
			if(condvar){
				conditional_node->equal_cond->lhs_value = condvar;
				condvar->dfgnode_out = dfg_node;
			}
			else{
				conditional_node->equal_cond->lhs_value = new DeclareData;
				assign_value(conditional_node->equal_cond->lhs_value,gnode->always_node->CaseBlock->condition_var);
			}
			conditional_node->equal_cond->rhs_value = new DeclareData;
			Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,conditional_node->equal_cond->rhs_value,NULL,NULL,NULL);
			conditional_node->equal_cond->rhs_value->name = case_expr->case_value;
			conditional_node->assign_expr = new Equal_to_op;
			Initialize_structures(NULL, NULL,NULL,NULL,conditional_node->assign_expr,NULL);
			conditional_node->assign_expr->lhs_value = new DeclareData;
			if(case_expr->expression_ct){
				assign_value(conditional_node->assign_expr->lhs_value,case_expr->expression_ct->left_value);
				conditional_node->assign_expr->rhs_value = new DeclareData;
				Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,conditional_node->assign_expr->rhs_value,NULL,NULL,NULL);
				conditional_node->assign_expr->rhs_value->name = case_expr->expression_ct->const_expr;
			}
			else{
				assign_value(conditional_node->assign_expr->lhs_value,case_expr->expression_vt->left_value);
				conditional_node->assign_expr->rhs_value = new DeclareData;
				assign_value(conditional_node->assign_expr->rhs_value, case_expr->expression_vt->right_value);
			}
			if(!dfg_node->condition_op)
				dfg_node->condition_op = conditional_node;
			else
				insert_in_condition_list(conditional_node,dfg_node);
			
			case_expr = case_expr->next_n;
		}
		dfg_node->output = conditional_node->assign_expr->lhs_value;
	}
}


}

//function to connect the rhs value of every clocked transitions(registers) with the already formed output nodes from the petrinet model
//RULE 6 to search for the lhs value of the assign node's state and connect it to the state
//EDITING
void Attach_clocked_transitions(Graph_node *graph_first_node,State_var *first_state,bool parallelplace_attach){

Transition_block *tran_tr=NULL;
Transition_block *prev_trans=NULL;
Place_block *newplace=NULL, *tmp_pl = NULL;
DeclareData *prev_data=NULL;
State_var *stateinput=NULL;
bool loop_create = false;

tran_tr = first_place_node->first_trans_node;

while(tran_tr){
	prev_trans = NULL;prev_data = NULL;
	if(tran_tr->data_node->assignment_graph && (Search_OutputVarFrom_Places(tran_tr->data_node->assignment_graph->rhs_value,first_place_node,prev_trans,newplace,NULL,prev_data,graph_first_node,first_state,true,loop_create,true)||Search_OutputVarFrom_Places(tran_tr->data_node->assignment_graph->rhs_value,first_parallel_place,prev_trans,newplace,NULL,prev_data,graph_first_node,first_state,true,loop_create,true))){
		
		if(prev_trans){
			if(prev_trans->output_var->transition_out)
				Insert_in_output_transition_list(prev_trans->output_var,tran_tr);
			else prev_trans->output_var->transition_out = tran_tr;
		}
		else if(prev_data){
			if(prev_data->transition_out)
				Insert_in_output_transition_list(prev_data,tran_tr);
			else prev_data->transition_out = tran_tr;
		}
		
	}
	//to connect the first place node with the appropriate state node
	if(Trace_Output_for_State_Place(tran_tr->output_var,stateinput)){// if the lhs value of assignment graph is traced forward to the place which has a state
		if(!first_place_node->state_place_input) first_place_node->state_place_input = stateinput->state_name;
		else Insert_placeInput_list( first_place_node, stateinput->state_name,false);
		if(!stateinput->state_name->place_ptr) stateinput->state_name->place_ptr = first_place_node;
		else  Insert_place_in_list(stateinput->state_name,first_place_node);
	}
	tran_tr = tran_tr->next_trans_node;
}

if(parallelplace_attach){
	//Here,it should search for outvar in the variables in var_list stored until now as inputs,and if found, replace outvar as variable in the list.
	tmp_pl = first_parallel_place;
	while(tmp_pl){
		if(Search_input_in_graph(tmp_pl->first_trans_node->output_var,first_state))
			tmp_pl->first_trans_node->data_node->output = tmp_pl->first_trans_node->output_var;
			
		tmp_pl = tmp_pl->next_place;
	}
	
}

}



//this fn will check var with all the vars in the var_list. if Yes, then remove the var and replace it with the matched variable in var_list.
// this uses both var_char and varinput_list to search the names
//list_num is for varinput_list
//char_num is for var_char
bool Search_input_in_graph(DeclareData*& var,State_var *first_state){

Transition_block *tmp_tr = NULL;
int i=0;
bool flag = false;

while(varinput_list[i] && i<= list_num){

	if(!strcmp(var->name,varinput_list[i]->name)){
		Delete_var_node(var);
		var = varinput_list[i];
		flag = true;
		break;
	}
	i++;
}
i=0;
/*
while(!flag && var_char[i] && i<= char_num){
	if(!strcmp(var->name,var_char[i])){
		var->name = var_char[i];
		flag = true;
		break;
	}
	i++;
}
*/
// this part is to check the input of the clocked transition nodes
if(!flag){
	tmp_tr = first_place_node->first_trans_node;
	while(tmp_tr){
		if(!strcmp(var->name, tmp_tr->data_node->assignment_graph->rhs_value->name)){
			flag = true;
			tmp_tr->data_node->assignment_graph->rhs_value->transition_out = tmp_tr;
			Delete_var_node(var);
			var = tmp_tr->data_node->assignment_graph->rhs_value;
			break;
		}
		tmp_tr = tmp_tr->next_trans_node;
	}
}


return flag;

}



//function to trace the clocked transition output to find the state node it should be connected to
bool Trace_Output_for_State_Place(DeclareData *searchvar,State_var *&state){

bool flag = false;
DeclareData *var=NULL;
DeclareData *tmp=NULL;
DeclareData *outvar=NULL;
Place_block *tmp_pl=NULL;

var = searchvar;

while(var){
	if(var->place_ptr){
		
		if(var->place_ptr->state_place_input ){
			tmp = var->place_ptr->state_place_input;
			flag = true;
		}
		if(!flag){
		//if no state in the connected place, then search for the state node connecte to the other place inputs of the connected place
			tmp = var->place_ptr->first_place_input;
			while(tmp){
				tmp_pl=Search_place_of_input(first_state,true,NULL,tmp,outvar,false,NULL);
				if(tmp_pl->state_place_input){
					tmp = tmp_pl->state_place_input;
					flag = true;
				}
			}
		}
		if(flag){
			while(tmp){
				//state is given a value in this function
				if(Search_var_from_statelist(tmp,state,false))
				{
					flag=true;
					break;
				}
				tmp = tmp->next_n;
			}
		
		}
	}
	if(!flag && var->operator_out)
		var = var->operator_out->output_value;
	
	if(!flag && var->equal_op_out)
		var = var->equal_op_out->lhs_value;
	

	else var=NULL;
}


return flag;
}









//function to insert the assign expressions(operations, and value assignments) in this petri graph
//for operation nodes, consisting of either wires or state signals, they r converted into signal selector nodes
void Attach_AssignNode_toDFG( DeclareData *varsearch,bool flag,Graph_node *graph_first_node,State_var *first_state,Compare_operator*& comparator,bool delflag,bool check_FUmodule){

Operate_op *operate_assign=NULL;
Assign_var *tmpassign=NULL ,*tmpassign_next = NULL ;
Assign_const *tmpconst = NULL , *tmpconst_next=NULL;
bool attachflag = false, inputon=false, flag1=false , flag2=false ,flag3=false , attach_output = false , loop_create = false,firstflag = true ;
Operate_node *tmpoper = NULL , *tmpoper_next=NULL;
Operate_op *operation_node=NULL ,*operate1 =NULL , *operate2=NULL ;
Ifthenelse_block *condnode=NULL , *condnode_next=NULL;
Place_block *newplace=NULL; //no need here, just to pass as null argument
Transition_block *trnode = NULL , *prevtr = NULL;
DeclareData *prevout = NULL ,*prev_data =NULL, *tmp = NULL , *node=NULL , *tmpnull = NULL, *dnode = NULL;
State_var *statevar=NULL;

//for assign nodes

if(graph_first_node->varassign_node){
	for(tmpassign = graph_first_node->varassign_node ; tmpassign!=NULL ; tmpassign = tmpassign_next){

		prevtr=NULL; prev_data=NULL;statevar = NULL;
		if( Search_OutputVarFrom_Places(tmpassign->right_value , first_place_node , prevtr,newplace,NULL,prev_data,graph_first_node,first_state,true,loop_create,true) || (tmpassign->right_value->data_type == input) ||(Search_var_from_statelist(tmpassign->right_value,statevar,false)) || Search_OutputVarFrom_Places(tmpassign->right_value,first_parallel_place,prevtr,newplace,NULL,prev_data,graph_first_node,first_state,true,loop_create,true)){
			//if the tmpassign is already created, then skip this iteration
			if((prev_data && Search_node_Loop(NULL,prev_data,NULL,tmpassign,tmpnull)) || (prevtr &&  Search_node_Loop(NULL,prevtr->output_var,NULL,tmpassign,tmpnull)) || (statevar && Search_node_Loop(NULL,statevar->state_name,NULL,tmpassign,tmpnull))){
				tmpassign_next = tmpassign->next_n;
				if(delflag) Delete_assign_node(graph_first_node,tmpassign);
				continue;
			}
			
			Equal_to_op *assign_op = new Equal_to_op;
			Initialize_structures(NULL, NULL,NULL,NULL,assign_op,NULL);
			//RULE 3
			 if(prev_data){
			 	if(!prev_data->equal_op_out) prev_data->equal_op_out = assign_op;
			 	else Insert_in_equalto_list(NULL,prev_data,assign_op);
			 	assign_op->rhs_value = prev_data;
			 }
			else if(prevtr){
				if(!prevtr->output_var->equal_op_out) prevtr->output_var->equal_op_out = assign_op;
				else Insert_in_equalto_list(NULL,prevtr->output_var,assign_op);
				 assign_op->rhs_value = prevtr->output_var;
			}	
			else if(statevar){
				if(!statevar->state_name->equal_op_out) statevar->state_name->equal_op_out = assign_op;
				else Insert_in_equalto_list(NULL,statevar->state_name,assign_op);
				assign_op->rhs_value = statevar->state_name;
			}
			else if(first_parallel_place || tmpassign->right_value->data_type==input){ //for input variables and parallel equalto nodes
				assign_op->rhs_value = new DeclareData;
				Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,assign_op->rhs_value,NULL,NULL,NULL);
				assign_value(assign_op->rhs_value, tmpassign->right_value);
				Insert_in_equalto_list(assign_op,NULL,NULL);
			}
			
			//LAST EDITING
			assign_op->lhs_value = new DeclareData;//tmpassign->left_value;
			assign_value(assign_op->lhs_value,tmpassign->left_value);
			if(Search_input_in_graph(assign_op->lhs_value,first_state))
				attach_output = true;
			assign_op->opsymbol = '=';
			attachflag = true;
			tmpassign_next = tmpassign->next_n; 
			
			if(delflag) Delete_assign_node(graph_first_node,tmpassign);
			
		}
		//else if(check_FUmodule){
		//	Search_varFrom_FU_Modules(graph_first_node->module_inst_node ,NULL,graph_first_node,first_state,false);
			//tmpassign_next = tmpassign->next_n;
		//}
		else
		tmpassign_next = tmpassign->next_n; 
	}
}

if(graph_first_node->constassign_node){

	for(tmpconst = graph_first_node->constassign_node ; tmpconst!=NULL ; tmpconst = tmpconst_next){

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


// this must be a conditional node with just then_var, which is changed in the function of create_nodes
//thus its in the list of graph nodes
if(graph_first_node->ifthenelse_node){

	condnode = graph_first_node->ifthenelse_node;
	while(condnode){
		comparator = new Compare_operator;
		Initialize_nodes(NULL,comparator,NULL,NULL,NULL,NULL);
		trnode = NULL;prev_data = NULL;
		if(condnode->equal_condition && Search_OutputVarFrom_Places(condnode->equal_condition->left_value,first_place_node,trnode,newplace,NULL,prev_data,graph_first_node,first_state,true,loop_create,true)){
			
			//if the condnode has equal condition, then the comparator just has value_out(control signal)
			if(condnode->then_var){
				comparator->value_out = new DeclareData;
				assign_value(comparator->value_out,condnode->then_var);
			}
			
			if(trnode){
				if(!trnode->output_var->comparator_out)
					trnode->output_var->comparator_out = comparator;
				else insert_in_operator_list(trnode->output_var,NULL,NULL,false,comparator,true);
				comparator->lhs_compare = trnode->output_var;
				
			}
			else if(prev_data){
				if(!prev_data->comparator_out) prev_data->comparator_out = comparator;
				else insert_in_operator_list(prev_data,NULL,NULL,false,comparator,true);
				comparator->lhs_compare = prev_data;
			}
			
			flag1=true;
			//the comparator must compare this value with the lhs_compare
			comparator->value_compare = condnode->equal_condition->const_expr;
		}
		else if(condnode->in_control_operation){
			node = condnode->in_control_operation->input_list->first_port;
			firstflag = true;
			while(node){
				prev_data = NULL;trnode = NULL;
				if(Search_OutputVarFrom_Places(node,first_place_node,trnode,newplace,NULL,prev_data,graph_first_node,first_state,true,loop_create,true) || Search_var_InStateList(node,first_state)){
					flag1 = true;
					if(firstflag){
						firstflag = false;
						comparator->value_out = new DeclareData;
						assign_value(comparator->value_out,condnode->then_var);
					}
					if(trnode){
						if(!trnode->output_var->comparator_out)
							trnode->output_var->comparator_out = comparator;
						else
							insert_in_operator_list(trnode->output_var,NULL,NULL,false,comparator,true);
						if(!comparator->condition_value) comparator->condition_value = trnode->output_var;
						else Insert_var_list(comparator->condition_value,trnode->output_var);
					}
					else if(prev_data){
						if(!prev_data->comparator_out) prev_data->comparator_out = comparator;
						else insert_in_operator_list(prev_data,NULL,NULL,false,comparator,true);
						
						if(!comparator->condition_value) comparator->condition_value = prev_data;
						else Insert_var_list(comparator->condition_value,prev_data);
					}
					else if(Search_var_from_statelist(node,statevar,false)){
						comparator->state_condition = statevar;
						if(!statevar->state_name->comparator_out) statevar->state_name->comparator_out=comparator;
						else insert_in_operator_list(statevar->state_name,NULL,NULL,false,comparator,true);
					}
				}
				else if(flag1 && !Check_node_from_array(varinput_list,list_num,node)){
					dnode = new DeclareData;
					 assign_value(dnode,node);
					 dnode->comparator_out = comparator;
					 varinput_list[list_num++] = dnode;
				}
				node = node->next_n;
			}
		}
		trnode = NULL;prev_data = NULL;
		//search for ifcondition var
		if(flag1 && condnode->if_condition_var){
			if(Search_OutputVarFrom_Places(condnode->if_condition_var,first_place_node,trnode,newplace,NULL,prev_data,graph_first_node,first_state,true,loop_create,true) || Search_var_InStateList(condnode->if_condition_var,first_state)){
				if(trnode){
					if(!trnode->output_var->comparator_out)
						trnode->output_var->comparator_out = comparator;
					else insert_in_operator_list(trnode->output_var,NULL,NULL,false,comparator,true);
					comparator->condition_value = trnode->output_var;
				}
				else if(prev_data){
					if(!prev_data->comparator_out) prev_data->comparator_out = comparator;
					else insert_in_operator_list(prev_data,NULL,NULL,false,comparator,true);
					comparator->condition_value = prev_data;
				}
				else if(Search_var_from_statelist(condnode->if_condition_var,statevar,false)){
					comparator->state_condition = statevar;
					if(!statevar->state_name->comparator_out) statevar->state_name->comparator_out=comparator;
					else insert_in_operator_list(statevar->state_name,NULL,NULL,false,comparator,true);
				}
			
				 flag2=true;
			}
			else if(!Check_node_from_array(varinput_list,list_num,condnode->if_condition_var)){
				  dnode = new DeclareData;
				  assign_value(dnode,condnode->if_condition_var);
				  dnode->comparator_out = comparator;
				  varinput_list[list_num++] = dnode;
			}
		}
		//delete the conditional nodes only if all the variables are attached
		if(flag1 || flag2){
			delete_nodes(NULL,tmpassign,tmpoper,condnode);
			condnode_next = condnode->next_block;
			if(condnode==graph_first_node->ifthenelse_node) graph_first_node->ifthenelse_node = condnode_next;
			else if(!condnode->next_block) condnode->prev_block->next_block = NULL;
			else{
				condnode->prev_block->next_block = condnode->next_block;
				condnode->next_block->prev_block = condnode->prev_block;
			}
			delete condnode;condnode=NULL;
			
			condnode = condnode_next;
		}
		else if(!flag1 && !flag2){
			delete comparator; comparator = NULL;
			 condnode=condnode->next_block;
		}
		else  condnode=condnode->next_block;
	}	

}


if(graph_first_node->operation_node){
	//convert all the operation nodes to the signal_selector node
	tmpoper = graph_first_node->operation_node;
	while(tmpoper){
		Signal_selector *select_node = new Signal_selector;
		Initialize_nodes(select_node,NULL,NULL,NULL,NULL,NULL);
		
		tmp = tmpoper->input_list->first_port;
		while(tmp){
			trnode=NULL;prev_data=NULL;
			if(Search_OutputVarFrom_Places(tmp,first_place_node,trnode,newplace,NULL,prev_data,graph_first_node,first_state,true,loop_create,true) || Search_var_InStateList(tmp,first_state)){
				inputon = true;
				//tmp = tmp->next_n;
				//continue;
			}
			else{
				inputon=false;
				break;
			}
			tmp=tmp->next_n;
		}
		if(inputon){
			select_node->out_signal = new DeclareData;
			assign_value(select_node->out_signal,tmpoper->output);
		}
		tmp = tmpoper->input_list->first_port;
		while(tmp && inputon){
			trnode = NULL;prev_data = NULL;
			if((Search_OutputVarFrom_Places(tmp , first_place_node , trnode , newplace, NULL , prev_data,graph_first_node,first_state,true,loop_create,true)) || (Search_var_InStateList(tmp, first_state))){
			
				if(trnode){
					if(!trnode->output_var->signal_selector_out)
						trnode->output_var->signal_selector_out = select_node;
					else insert_in_operator_list(trnode->output_var,NULL,select_node,false,NULL,false); //this function works for signal selectors also
					if(!select_node->in_signal_list) select_node->in_signal_list = trnode->output_var;
					else Insert_var_list(select_node->in_signal_list,trnode->output_var);
				}
				else if(prev_data){
					if(!prev_data->signal_selector_out)
						prev_data->signal_selector_out = select_node;
					else insert_in_operator_list(prev_data,NULL,select_node,false,NULL,false);
					if(!select_node->in_signal_list) select_node->in_signal_list = prev_data;
					else Insert_var_list(select_node->in_signal_list,prev_data);
				}
				else if(Search_var_from_statelist(tmp,statevar,false)){
					if(!select_node->state_in_signal) select_node->state_in_signal = statevar->state_name;
					else Insert_var_list(select_node->state_in_signal, statevar->state_name);
					
					if(!statevar->state_name->signal_selector_out) statevar->state_name->signal_selector_out = select_node;
					else insert_in_operator_list(statevar->state_name,NULL,select_node,false,NULL,false);
					//else Insert_selector_list(statevar,select_node);
				}
				
			}
			tmp = tmp->next_n;
		}
		if(inputon){
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
			tmpoper = tmpoper_next;
		}
		else{
			delete select_node ; select_node = NULL;
			 tmpoper = tmpoper->next_op;
		}
	}
}

} //end of function
	
	
//function to create DFG from ifthenelse conditional block of always block
//loopinput is sent if the node before it was created during a loop and loopcheck = false. loopcheck to indicate if its being called during loop creation
//condcheck is sent when only one particular condnode is to be created amongst other condnodes under the placenode, if condcheck is null, then create all the conditional nodes of alwaysnode under dfgnode
void Create_DFG_from_ifthenelse( DFG_block *dfgnode , Ifthenelse_block *condexpr , DeclareData *outvarnode,Graph_node *graph_first_node,State_var *first_state,bool loopcheck,DeclareData *loopinput,Ifthenelse_block *condcheck,bool output_exists){

Transition_block *prev_tr = NULL , *prevtran = NULL;
Condition_block *condop= NULL;
DeclareData *prev_out = NULL , *prevot = NULL,*outvar = NULL;
Place_block *place_node = NULL;
State_var *state_ret=NULL;
bool loop_create = false , outvarcheck = false;
//bool output_exists = false;

if(condcheck)
	condexpr = condcheck;

while(condexpr){
	prev_out = NULL;prev_tr = NULL; prevtran = NULL;prevot = NULL;
	if(condcheck) outvarcheck = false;
	else if(!condexpr->prev_block) outvarcheck = false;
	else outvarcheck = true;

	condop = new Condition_block;
	Initialize_structures(condop , NULL,NULL,NULL,NULL,NULL);
	if(!loopcheck && loopinput && !strcmp(loopinput->name,condexpr->if_condition_var->name))
		condop->if_cond_var = loopinput;
	else if(Search_var_from_statelist(condexpr->if_condition_var,state_ret,false))
		condop->if_cond_var = state_ret->state_name;
		
	else if(loopcheck && Search_OutputVarFrom_Places(condexpr->if_condition_var,first_place_node, prevtran , place_node ,NULL,prevot,graph_first_node,first_state,loopcheck,loop_create,true)){	
		if(prevtran)
			condop->if_cond_var = prevtran->output_var;
		else if(prevot)
			condop->if_cond_var = prevot;
	}
	else if(!loopcheck){
		condop->if_cond_var = new DeclareData;
		assign_value(condop->if_cond_var , condexpr->if_condition_var);
		//varinput_list[list_num++] = condop->if_cond_var;
	}
	if(condexpr->then_expr_var){
		condop->assign_expr = new Equal_to_op;
		Initialize_structures(NULL, NULL,NULL,NULL,condop->assign_expr,NULL);
		//attach the output
		 if(outvar)
			condop->assign_expr->lhs_value = outvar;
		else if(output_exists)
			condop->assign_expr->lhs_value = outvarnode;
		
		/*else if(Search_OutputVarFrom_Places(condexpr->then_expr_var->left_value,first_place_node,prev_tr,place_node,NULL,prev_out,graph_first_node,first_state,loopcheck,loop_create,true)){
			output_exists = true;
			if(prev_out)
				condop->assign_expr->lhs_value = prev_out;
			else if(prev_tr)
				condop->assign_expr->lhs_value = prev_tr->output_var;
		}*/
		else if(!outvarcheck){
			condop->assign_expr->lhs_value = new DeclareData;//condexpr->then_expr_var->left_value;
			assign_value(condop->assign_expr->lhs_value , condexpr->then_expr_var->left_value );
			outvar = condop->assign_expr->lhs_value;
		}
		prev_tr = NULL;prev_out = NULL;
		if(!loopcheck && loopinput && !strcmp(condexpr->then_expr_var->right_value->name,loopinput->name))
			condop->assign_expr->rhs_value = loopinput;
		else if(loopcheck & Search_OutputVarFrom_Places(condexpr->then_expr_var->right_value,first_place_node,prev_tr,place_node,NULL,prev_out,graph_first_node,first_state,loopcheck,loop_create,true)){
			if(prev_tr) condop->assign_expr->rhs_value = prev_tr->output_var;
			else if(prev_out) condop->assign_expr->rhs_value = prev_out;
		}
		else{
			condop->assign_expr->rhs_value = new DeclareData;//condexpr->then_expr_var->right_value;
			assign_value(condop->assign_expr->rhs_value , condexpr->then_expr_var->right_value ); 
			if(condexpr->then_expr_var->right_value->data_type == integer)
				condop->assign_expr->rhs_value->data_type = integer;
		}
		condop->assign_expr->opsymbol = '=';
	}
	
	if(!dfgnode->condition_op) dfgnode->condition_op = condop;
	else insert_in_condition_list(condop,dfgnode);
	
	
	if(condcheck) break;
	else condexpr = condexpr->else_expr_block;

}
	//output will be added only once
	
/*	if(output_exists){
		delete outvarnode; outvarnode = NULL;
		outvarnode = condop->assign_expr->lhs_value;
	}
	else*/
	if(!output_exists)	
		assign_value(outvarnode , condop->assign_expr->lhs_value);
	
	
		
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
		Create_DFG_from_operateexpr( flownode , temp->operate_expr , output,false,false);
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
	Select_from_operator_list(nextop1 ,NULL, temp->comp_expr->basic_op1->operator_type);
	Select_from_operator_list(nextop2 ,NULL, temp->comp_expr->basic_op2->operator_type);

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
	 Select_from_operator_list(nextop3 , NULL,temp->comp_expr->operator_type);
	 
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
	Select_from_operator_list(tmp_op ,NULL, temp->comp_expr->basic_op1->operator_type);
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
	Select_from_operator_list(tmp_op1 ,NULL, temp->comp_expr->basic_op2->operator_type);
	
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
	Select_from_operator_list(final_op ,NULL, temp->comp_expr->operator_type);
	
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

void Create_DFG_from_operateexpr( DFG_block *datanode , Operate_node *opnode , DeclareData *output,bool outputflag,bool loopcheck){

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
	Select_from_operator_list(tempop ,NULL,  tmpn->operator_type);


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
void Create_DFG_from_assignexpr( DFG_block *dnode , Assign_var *expr, DeclareData*& output,Graph_node *graph_first_node,State_var *first_state,bool nullalways,bool loopcheck){


Place_block *place_node = NULL;
DeclareData *prev_out = NULL;
Transition_block *prev_tr  = NULL;
bool loop_create=  false;

Equal_to_op *equal_assign = new Equal_to_op;
Initialize_structures(NULL, NULL,NULL,NULL,equal_assign,NULL);


	if(nullalways){
		equal_assign->rhs_value = new DeclareData; //expr->left_value;
		assign_value(equal_assign->rhs_value, expr->right_value);
		
	}
	else if(Search_OutputVarFrom_Places(expr->right_value,first_place_node, prev_tr , place_node ,NULL,prev_out,graph_first_node,first_state,loopcheck,loop_create,true)){
		if(prev_tr) equal_assign->rhs_value = prev_tr->output_var;
		else if(prev_out) equal_assign->rhs_value = prev_out;
	}
	
	equal_assign->opsymbol = '=';
	
	//this case is for scenario when two similar nodes give rise to one output, thus here it wil check if previous nodes, have the same output, then link this to the previous nodes
	if(!nullalways && Search_OutputVarFrom_Places(expr->left_value, first_place_node, prev_tr , place_node ,NULL,prev_out,graph_first_node,first_state,loopcheck,loop_create,true)){
		if(prev_tr)
			equal_assign->lhs_value = prev_tr->output_var;
		else if(prev_out)
			equal_assign->lhs_value = prev_out;
	}
	else{
		equal_assign->lhs_value = new DeclareData; //expr->left_value;
		assign_value(equal_assign->lhs_value , expr->left_value);
	}
	
		output = equal_assign->lhs_value; //the output of dfg is the same as output of the equal_assign
	//output = expr->left_value; // assign the output_var of the transition node
	
	dnode->assignment_graph = equal_assign;
	dnode->output = output;
//}

//else{
	
//	Create_DFG_from_operateexpr( dnode , expr->operation_rhs , output,true,loopcheck);
//}


}


//function to insert the equalto node in the list
//only for the parallel nodes
void Insert_in_equalto_list(Equal_to_op *assign_node , DeclareData *parent_node , Equal_to_op *insert_node){

Equal_to_op *tmp=NULL;

if(assign_node){
	if(!first_EqualTo_node){
		first_EqualTo_node = assign_node;
		assign_node->prev_equal=NULL;
		assign_node->next_equal=NULL;
	}
	else{
		for(tmp=first_EqualTo_node ; tmp->next_equal!=NULL;tmp = tmp->next_equal);
		tmp->next_equal = assign_node;
		assign_node->prev_equal = tmp;
		assign_node->next_equal=NULL;
	}
}
else if(insert_node){

	for(tmp = parent_node->equal_op_out ; tmp->next_equal!=NULL; tmp=tmp->next_equal);
	tmp->next_equal = insert_node;
	insert_node->next_equal=NULL;
	insert_node->prev_equal = tmp;
}


}

//function to insert extra condition vars of a conditional block, this works only if there are multiple state variables for resulting one signal in always node
void Insert_var_list(DeclareData *firstvar,DeclareData *varto){

DeclareData *tmp=NULL;

for(tmp = firstvar;tmp->next_n!=NULL;tmp = tmp->next_n);

tmp->next_n = varto;
varto->prev_n = tmp;
varto->next_n=NULL;

}

//function to initialize the nodes

void Initialize_nodes(Signal_selector *node,Compare_operator *node1, State_var *node2,Control_block *node3,Basic_block *node4,Mux_node *node5){

if(node){
node->in_signal_list=NULL;
node->state_in_signal=NULL;
node->out_signal=NULL;
node->next_selector=NULL;
}
if(node1){
	node1->lhs_compare=NULL;
	node1->condition_value=NULL;
	node1->state_condition=NULL;
	node1->value_compare=NULL;
	node1->value_out=NULL;
	node1->opsymbol = '\0';
	node1->next_comparator=NULL;
}
if(node2){
	node2->next_state=NULL;
	node2->prev_state=NULL;
	node2->state_name=NULL;
	node2->signal_selector_out=NULL;
}
if(node3){
	node3->bb_ptr=NULL;
	node3->state_node=NULL;
	node3->next_control_block=NULL;
	node3->prev_control_block=NULL;
	node3->control_dfg_node=NULL;
	node3->control_compare_node=NULL;
	node3->signal_select_node=NULL;
	node3->control_in_from_dfg=NULL;
	//node3->control_in=NULL;
	node3->result_control=NULL;
	node3->control_out=NULL;
	Initialize_control_pointers(node3->control_in_pointers,10);
}
if(node4){
	Initialize_control_pointers(node4->control_node_pointers,10);
	//node4->control_node_pointers=NULL;
	//node4->first_OperTree_node=NULL;
	node4->first_block_input=NULL;
	node4->first_block_output=NULL;
	node4->multiplexer=NULL;
	node4->next_block = NULL;
	node4->prev_block = NULL;
}
if(node5){
	node5->enable_signal=NULL;
	node5->cond_expr=NULL;
	node5->output=NULL;
}
}


void Initialize_control_pointers(Control_block **node_ptr,int size){

int i=0;
for(i=0;i<size;i++)
	node_ptr[i] = NULL;



}





//function to insert a selector node in the list of outgoing selectors from statenode
void Insert_selector_list(State_var *statenode, Signal_selector *node_to_insert){

Signal_selector *tmp=NULL;
for(tmp = statenode->signal_selector_out;tmp->next_selector!=NULL; tmp = tmp->next_selector);

tmp->next_selector=node_to_insert;
node_to_insert->next_selector=NULL;

}


//EDITING HERE
//fn to insert an extra port in the module acc. to the gnode
void Insert_port_input(ModuleInstantiate*& module, Graph_node *graph_first_node){

Graph_node *gnode = NULL;
DeclareData *tmp = NULL;
DeclareData *inputn = NULL;
DeclareData *newdata = NULL;
gnode = graph_first_node;

for(tmp = module->ports_list->first_port ; tmp->next_n!=NULL;tmp = tmp->next_n){
	if(!tmp->next_n->next_n)
		break;
}

while(gnode){
	if(!strcmp(gnode->name,module->mod_name)){
		inputn = gnode->operation_node->input_list->first_port;
		while(inputn){
			if(inputn->data_type == integer){
				newdata = new DeclareData;
				assign_value(newdata,inputn);
				newdata->next_n = tmp->next_n;
				newdata->prev_n = tmp;
				tmp->next_n = newdata;	
				break;
			}
			inputn = inputn->next_n;	
		}
	}
	gnode = gnode->next_node;

}




}



//to search for variables in the state list
//and to search for operations attached to the variable in statel ist
bool Search_var_from_statelist( DeclareData *var , State_var*&svar,bool cond){

State_var *tmp=NULL;
bool flag=false;
tmp = first_state;

if(!cond){
	while(tmp){
		if(!strcmp(var->name,tmp->state_name->name )){
			flag = true;
			svar = tmp;
			break;
		}
		tmp = tmp->next_state;
	
	}
}

return flag;
}





//function to search clocked always nodes
void search_for_always_node(Graph_node *graph_start_node , bool search_first_node , bool search_node){

Graph_node *temp = NULL;
Always_block *temp_always = NULL;
Always_block *node = NULL;
DeclareData *tempnode=NULL;

// this is for searching the always node having null event controls only
if(search_first_node){

for(temp_always = graph_start_node->always_node ; temp_always !=NULL; temp_always = temp_always->next_n){

	if(temp_always->event_controls == NULL){
	
		if(temp_always->CondBlock){
			temp_always->event_controls = new PortList;
			 Initialize_values(NULL, temp_always->event_controls,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
			tempnode = new DeclareData;
			 Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,tempnode,NULL,NULL,NULL);
			 assign_value(tempnode,temp_always->CondBlock->if_condition_var);
			 insert_in_list(temp_always->event_controls, tempnode);
			 continue;
		}
		else{
			// create the list for all the first always nodes
			node = new Always_block;
			Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,node,NULL,NULL,NULL,NULL);
			*node = *temp_always;
			insert_in_null_always_list(node);
		}
	}
		
	else
	continue;
}

}

else{
}

}

//function to insert tmpnode in the list of the comparators(start node is node)
void Insert_in_compare_list(Compare_operator *node,Compare_operator *tmpnode){

Compare_operator *tmp= NULL;

for(tmp = node ; tmp->next_comparator!=NULL;tmp = tmp->next_comparator);
tmp->next_comparator = tmpnode;
tmpnode->next_comparator=NULL;

}


//function to insert operators or signal selectors connected to a variable


void insert_in_operator_list( DeclareData *out, Operate_op *op_insert, Signal_selector *node , bool flag,Compare_operator *compnode,bool compflag){

Operate_op *tmp=NULL;
Signal_selector *tmps=NULL;
Compare_operator *tmpcomp=NULL;

if(flag){
	for(tmp = out->operator_out ; tmp->next_oper!=NULL; tmp = tmp->next_oper);
	
	tmp->next_oper  = op_insert;
	op_insert->prev_oper = tmp;
	op_insert->next_oper = NULL;

//	out->next_operator_out = true;
}
else if(!flag && !compflag){
	for(tmps = out->signal_selector_out;tmps->next_selector!=NULL; tmps=tmps->next_selector);
	tmps->next_selector = node;
	node->next_selector=NULL;
	//out->next_selector_out=true;
}
else if(compflag && !flag){
	for(tmpcomp = out->comparator_out;tmpcomp->next_comparator!=NULL;tmpcomp = tmpcomp->next_comparator);
	tmpcomp->next_comparator = compnode;
	compnode->next_comparator=NULL;
	//out->next_comparator_out=true;
}


}


//function to insert an always node in between the list of always nodes after the position of tmp always node
void Insert_between_alwayslist(Always_block *tmp,Always_block *always_temp,Graph_node *graph_first_node){

Always_block *iter=NULL;

iter = graph_first_node->always_node;
while(iter){
	if(tmp == iter){
		always_temp->next_n = tmp->next_n;
		always_temp->prev_n = tmp;
		tmp->next_n = always_temp;
		break;
	}
	iter = iter->next_n;
}

}

//function to insert a transition path connecting to the output of a dfg node
void Insert_in_output_transition_list(DeclareData *var,Transition_block *trantmp){

Transition_block *tn=NULL;

for(tn=var->transition_out; tn->next_trans_node!=NULL;tn = tn->next_trans_node);
tn->next_trans_node = trantmp;
trantmp->prev_trans_node = tn;
trantmp->next_trans_node=NULL;


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
	
	
	
	
void Select_from_operator_list(Operate_op *tempop ,ModuleInstantiate *modop, unsigned operator_type){



switch(operator_type){

case VERI_REDAND:
{
	if(tempop) tempop->op_type = '&';
	else if(modop) modop->optype = '&';
	break;
}
case VERI_REDOR:
{
	if(tempop) tempop->op_type = '|';
	else if(modop) modop->optype = '|';
	break;
}
case VERI_REDNAND:
{
	if(tempop) tempop->op_type = '~&';
	else if(modop) modop->optype = '~&';
	break;
}
case VERI_REDXOR:
{
	if(tempop) tempop->op_type = '^';
	else if(modop) modop->optype = '^';
	break;
}
case VERI_REDNOR:
{
	if(tempop) tempop->op_type = '~|';
	else if(modop) modop->optype = '~|';
	break;
}
case VERI_PLUS:
{
	if(tempop) tempop->op_type = '+';
	else if(modop) modop->optype = '+';
	break;
}
case VERI_MIN:
{
	if(tempop) tempop->op_type = '-';
	else if(modop) modop->optype = '-';
	break;
}
case VERI_MUL:

case VERI_AND:
{
	if(tempop) tempop->op_type = '*';
	else if(modop) modop->optype = '*';
	break;
}
case VERI_DIV:
{
	if(tempop) tempop->op_type = '/';
	else if(modop) modop->optype = '/';
	break;
}
case VERI_OR:
{
	if(tempop) tempop->op_type = '|';
	else if(modop) modop->optype = '|';
	break;
}
case VERI_LT:
{
	if(tempop) tempop->op_type = '<';
	else if(modop) modop->optype = '<';
	break;
}
case VERI_GT:
{
	if(tempop) tempop->op_type = '>';
	else if(modop) modop->optype = '>';
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
			/*if(tmp_d->CondBlock->then_expr_const) {delete tmp_d->CondBlock->then_expr_const; tmp_d->CondBlock->then_expr_const=NULL;}*/
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
		node3->state_place_input=NULL;
		node3->first_trans_node=NULL;
		node3->next_place=NULL;
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
		node5->next_equal=NULL;
		node5->prev_equal=NULL;
	}
	else if(node6){
		node6->opnode=NULL;
		node6->varnode=NULL;
		node6->assignnode = NULL; 
		node6->alnode = NULL;
		node6->modnode = NULL;
		node6->condnode = NULL;
		node6->casenode = NULL;
		//node6->placenode=NULL;
		//node6->trannode=NULL;
		//node6->equalnode=NULL;
		//node6->dfgnode=NULL;
	}
	
}

//fn to initialize the const char name elements stored in varchar
void Initialize_char(const char **varchar, int size){

int i;

for(i=0;i<size;i++)
	varchar[i] = NULL;

}




void delete_ports_list(PortList*& list){

DeclareData *tmpn=NULL;
//DeclareData *tmp_prev=NULL;
DeclareData *tmpn_next = NULL;

tmpn = list->first_port;

while(tmpn){
	tmpn_next = tmpn->next_n;
	if(tmpn == list->first_port){
		list->first_port = tmpn_next;
	//	tmpn_next->prev_n = NULL;
	}
	else if(!tmpn->next_n)
		tmpn->prev_n->next_n = NULL;
	else{
		tmpn->next_n->prev_n = tmpn->prev_n;
		tmpn->prev_n->next_n = tmpn->next_n;
	}
	Delete_var_node(tmpn);
	tmpn = tmpn_next;
}

/*
for(tmpn = list->first_port; tmpn->next_n!=NULL;tmpn = tmpn->next_n);
tmp_prev = tmpn;
while(tmp_prev){

	tmpn = tmp_prev;
	tmp_prev = tmpn->prev_n;
	Delete_var_node(tmpn);
}
*/
delete list ; list=NULL;	

}


//fn to delete the "node" from equalto list in graph_first_node
void Delete_assign_node(Graph_node *graph_first_node,Assign_var*& node){

Assign_var *tmp = NULL;

tmp = graph_first_node->varassign_node;

if(node == graph_first_node->varassign_node) 
	graph_first_node->varassign_node = node->next_n;

else if(!node->next_n)
	node->prev_n->next_n = NULL;
else{
	
	//node_next = node->next_block;
	node->prev_n->next_n = node->next_n;
	node->next_n->prev_n = node->prev_n;
	
}

Delete_var_node(node->left_value);
Delete_var_node(node->right_value);

delete node;
node  = NULL;


}

//fn to delete a variable node
void Delete_var_node(DeclareData*& node){

node->operator_in = NULL;
node->operator_out = NULL;
node->signal_selector_out = NULL;
node->equal_op_out = NULL;
node->comparator_out = NULL;
node->transition_out = NULL;
node->dfgnode_out = NULL;
node->place_ptr = NULL;

delete node;
node = NULL;

}


//fn to remove the case item which has input as var, and remove in the event_controls so that search_back_parse_tree fn cannot search this

void Delete_case_node(Always_block*& tmpal,DeclareData *var,Graph_node *graph_first_node,Ifthenelse_block*& condnode){

DeclareData *tmp = NULL;
DeclareData *tmp_next = NULL;
Ifthenelse_block *tmpif = NULL;
Ifthenelse_block *tmpif_next = NULL;
Case_Statement *tmpc = NULL;
Case_Statement *tmpc_next = NULL;
ModuleInstantiate *tmpmod = NULL;
bool flag = false;

if(tmpal){
	if(tmpal->CaseBlock) tmpc = tmpal->CaseBlock->next_n; 
	tmp = tmpal->event_controls->first_port;
}
if(condnode)
	tmpif = condnode;
else
	tmpif = tmpal->CondBlock;

//here all the event controls should be deleted wich is related to tmpif
while(tmp){
	tmp_next = tmp->next_n;
	if(!strcmp(tmp->name,var->name) || (tmpif && Search_in_Cond_Block(tmp,tmpif))){
		
		if(tmp == tmpal->event_controls->first_port)
			tmpal->event_controls->first_port = tmp_next;
		else if(!tmp->next_n)
			tmp->prev_n->next_n = NULL;
		else{
			tmp->prev_n->next_n = tmp->next_n;
			tmp->next_n->prev_n = tmp->prev_n;
		}
		delete tmp;
		tmp = NULL;
		//break;
	}
	tmp = tmp_next;
}

while(tmpc){
	tmpc_next = tmpc->next_n;
	if(!strcmp(tmpc->expression_vt->right_value->name,var->name)){
		//if(tmpc == tmpc
		
		if(!tmpc->next_n)
			tmpc->prev_n->next_n = NULL;
		else{
			tmpc->prev_n->next_n = tmpc->next_n;
			tmpc->next_n->prev_n = tmpc->prev_n;
		}
		delete tmpc;
		tmpc = NULL;
		break;
	}
	tmpc = tmpc_next;
}

while(tmpif){
	if(tmpif->next_block)
		tmpif_next = tmpif->next_block;
	else tmpif_next = tmpif->else_expr_block;
	//EDITING HERE
	//CHANGED HERE
	if(!strcmp(tmpif->then_expr_var->right_value->name,var->name) || (tmpif == condnode)){
		
		if(tmpif->if_condition_var){
			delete tmpif->if_condition_var ; tmpif->if_condition_var = NULL;
		}
		else if(tmpif->equal_condition){
			Delete_var_node(tmpif->equal_condition->left_value);
			tmpif->equal_condition->const_expr = NULL;
			delete tmpif->equal_condition ; tmpif->equal_condition = NULL;
		}
		if(tmpif->then_expr_var){
			Delete_var_node(tmpif->then_expr_var->left_value);
			Delete_var_node(tmpif->then_expr_var->right_value);
			delete tmpif->then_expr_var;
			tmpif->then_expr_var = NULL;
		}	
		//write the logic for removing one else_Expr_block from the list of else_expr
		
		if(tmpif == tmpal->CondBlock){
		
			if(!tmpif->next_block)
				flag = true;
		//	if(tmpif->next_block)
			tmpal->CondBlock = tmpif_next;
			// if(tmpif->else_expr_block)
				//Insert_else_block(tmpal, tmpif->else_expr_block);
			
		}
		else{
			tmpal->CondBlock->else_expr_block = tmpif_next;
		
		}
		/*
		else if(!tmpif->next_block){
			tmpif->prev_block->next_block = NULL;
			//if(tmpif->else_expr_block)
			//	Insert_else_block(tmpal, tmpif->else_expr_block);
		}
		else{
			tmpif->prev_block->next_block = tmpif->next_block;
			tmpif->next_block->next_block = tmpif->prev_block;
			//if(tmpif->else_expr_block)
			//	Insert_else_block(tmpal, tmpif->else_expr_block);
		}
		*/
		
		delete tmpif;
		tmpif = NULL;
		break;
	}
	
	tmpif = tmpif_next;

}



}


//function to insert as else_block
void Insert_else_block(Always_block*& alnode, Ifthenelse_block *block){

Ifthenelse_block *tmp = NULL;

if(!alnode->CondBlock)
	alnode->CondBlock = block;
else if(!alnode->CondBlock->else_expr_block)
	alnode->CondBlock->else_expr_block = block;
else{
	for(tmp = alnode->CondBlock->else_expr_block ; tmp->else_expr_block!=NULL; tmp = tmp->else_expr_block);
	tmp->else_expr_block = block;
	block->else_expr_block = NULL;
}

}

//function to delete an entire list on request
//gnode is deleted from the end of the list
//snode is deleted from thestart of the list
void delete_data_list( Graph_node *gnode,State_var *snode){

DeclareData *gnext=NULL;
DeclareData *gnext_prev=NULL;
State_var *snext=NULL;

if(gnode){
	for(gnext=gnode->data_node ; gnext->next_n!=NULL ; gnext = gnext->next_n);
	gnext_prev = gnext;
	
	while(gnext_prev){
		
		gnext = gnext_prev ; 
		gnext_prev = gnext->prev_n;
		delete gnext ; gnext=NULL;
	}

}
else if(snode){
	while(snode){
		snext = snode->next_state;
		delete snode->state_name;
		snode->state_name=NULL;
		delete snode;
		snode=NULL;
	
	}
}
	
}

//delete the assign nodes which have state in their inputs
//delete a specified node on request
void delete_nodes(Graph_node *node, Assign_var*& vardel, Operate_node*& opdel,Ifthenelse_block*& conddel){

Assign_var *tmp=NULL;
Assign_var *tmp_next=NULL;
Operate_node *tmpop=NULL;
Operate_node *tmpop_next=NULL;


if(vardel){
	for(tmp = node->varassign_node ; tmp!=NULL; tmp = tmp_next){
		if(tmp == vardel){
			tmp_next = tmp->next_n;
			if(tmp == node->varassign_node) node->varassign_node = tmp_next;
			else if(!tmp->next_n) tmp->prev_n->next_n=NULL;
			else{
				tmp->prev_n->next_n = tmp->next_n;
				tmp->next_n->prev_n = tmp->prev_n;
			}
			delete tmp;
			tmp=NULL;
			break;
		}
		else tmp_next = tmp->next_n;
	}

}
else if(opdel){
	for(tmpop = node->operation_node ; tmpop!=NULL; tmpop = tmpop_next){
		if(tmpop == opdel){
			tmpop_next = tmpop;
			if(tmpop == node->operation_node) node->operation_node = tmpop_next;
			else if(!tmpop->next_op) tmpop->prev_op->next_op = NULL;
			else{
				tmpop->prev_op->next_op = tmpop->next_op;
				tmpop->next_op->prev_op = tmpop->prev_op;
			}
			delete tmpop;
			tmpop=NULL;
			break;
		}
		else tmpop_next = tmpop->next_op;
	}

}
else if(conddel){
	delete conddel->if_condition_var; conddel->if_condition_var=NULL;
	if(conddel->equal_condition){
		delete conddel->equal_condition->left_value ;conddel->equal_condition->left_value =NULL;
		conddel->equal_condition->const_expr = NULL;	
	}
	if(conddel->then_expr_var){
		delete conddel->then_expr_var->left_value; conddel->then_expr_var->left_value=NULL;
		delete conddel->then_expr_var->right_value; conddel->then_expr_var->right_value=NULL;
	}
	else if(conddel->then_var){
		delete conddel->then_var;conddel->then_var=NULL;
	}
	
}

}






//replace the event controls list of asynchronous reset always node with var(varassign) or if its oper then, replace the event controls list with 
void Replace_ports_list(Always_block *alnode,PortList*& eventlist , DeclareData *var, bool assign,Operate_node *oper, Graph_node *node){

DeclareData *tmpn = NULL , *tmpn_next=NULL,*tmpt = NULL ;
Ifthenelse_block *tmpnull = NULL;
Assign_var *tmp_null = NULL;

for(tmpn = eventlist->first_port ; tmpn!=NULL;tmpn=tmpn_next){

	tmpn_next = tmpn->next_n;
	if(tmpn == eventlist->first_port) eventlist->first_port = tmpn_next;
	else if(!tmpn->next_n) tmpn->prev_n->next_n = NULL;
	else{
		tmpn->prev_n->next_n = tmpn->next_n;
		tmpn->next_n->prev_n = tmpn->prev_n;
	}
	delete tmpn;
	tmpn = NULL;
}
	if(assign){
		
		tmpn = new DeclareData;
		assign_value(tmpn,var);
		 insert_in_list(eventlist , tmpn);
		 //also insert the rightvalue of the assign expr of the always node in event controls
		 tmpt = new DeclareData;
		 assign_value(tmpt, alnode->CondBlock->then_expr_var->right_value);
		 insert_in_list(eventlist,tmpt);
		 delete alnode->CondBlock->if_condition_var;
		 alnode->CondBlock->if_condition_var = new DeclareData;
		 assign_value(alnode->CondBlock->if_condition_var,var);
	}
	else{
		//this is for oper case
		tmpt = oper->input_list->first_port;
		while(tmpt){
		
			tmpn = new DeclareData;
			Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,tmpn,NULL,NULL,NULL);
			assign_value(tmpn,tmpt);
			 insert_in_list(eventlist , tmpn);
			// tmpn=new DeclareData;
			// Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,tmpn,NULL,NULL,NULL);
			// assign_value(tmpn,condvar);
			//  insert_in_list(eventlist , tmpn);
			tmpt = tmpt->next_n;
		}
		tmpt = new DeclareData;
		assign_value(tmpt,alnode->CondBlock->then_expr_var->right_value);
		insert_in_list(eventlist,tmpt);
		//delete the oper node here.
		//delete_nodes(node,tmp_null,oper,tmpnull);
	}



}


//fn to check if all the states in list_search are there in state_list, if yes then send true. if no, then insert that state in the state_place_input list which is state_list
bool Check_State_list(State_var** list_search,DeclareData *state_list,Place_block*& place,int size){

int i=0;
//int j=0;
bool search = false;
DeclareData *tmp = NULL;


while(list_search[i] && i<size){
	tmp = state_list;
	while(tmp){
		if(!strcmp(tmp->name, list_search[i]->state_name->name)){
			search = true;
			break;
		}
		else search = false;
		tmp = tmp->next_n;
	}
	if(!search){
		if(!place->state_place_input) place->state_place_input = list_search[i]->state_name;
		else Insert_placeInput_list(place,list_search[i]->state_name,false);
		if(!list_search[i]->state_name->place_ptr) list_search[i]->state_name->place_ptr = place;
		else Insert_place_in_list(list_search[i]->state_name,place);
		
	}

	i++;
	
return search;
}





}



//function to delete the path of loop nodes

void Delete_node_list(void){

int i=0;

while(i<10){

	if(node_list[i]){
		delete node_list[i];
		node_list[i]=NULL;
	}
	i++;
}


}



// to search a particular variable from the entire graph
//external call to this function varflag=false
//internal recursive call varflag = true
bool Search_var_from_graph( DeclareData *varsearch, DeclareData *vartemp,Transition_block *prevtr ,Compare_operator*& prevcomp,Signal_selector*& prev_sig,Operate_op*& prev_op,DeclareData*& prevout,State_var *state,bool varflag,bool send_value ){

bool search = false , node_down = false;
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
		prev_op = NULL;
			if(!varflag) vartemp = tmp_state->state_name;
			//vartemp = tmp_place->first_trans_node->output_var;
			while(vartemp){
				search = false; node_down = false;
				if(!strcmp(varsearch->name , vartemp->name)){
				
					if(send_value) prevout = vartemp;
					//if(tmpcomp) prevcomp = tmpcomp;
					//else if(tmpsig) prev_sig = tmpsig;
					search = true;
					break;
				}
			//	tmpcomp = NULL;
			//	tmpsig=NULL;
				if(!node_down && vartemp->comparator_out){
					
					node_down = true;
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
			
				if(!node_down && vartemp->operator_out){
					node_down = true;
					if(vartemp->operator_out->op_type == '<' || vartemp->operator_out->op_type == '>'){
						if(send_value) prev_op = vartemp->operator_out;
					}
					vartemp = vartemp->operator_out->output_value;
					continue;
				}	
				
				if(!node_down && vartemp->equal_op_out){
					node_down = true;
					vartemp = vartemp->equal_op_out->lhs_value;
					
				}	
				if(!node_down && vartemp->transition_out){
					
					trantmp = vartemp->transition_out;
					while(trantmp){
						if(Search_var_from_graph(varsearch,trantmp->output_var,prevtr,prevcomp,prev_sig,prev_op,prevout,tmp_state,true,send_value)){
							search=true;
							node_down = true;
							if(send_value) prevtr = trantmp;
							break;
						}
						else node_down = false;
						trantmp= trantmp->next_trans_node;
					}
					if(!search){
						vartemp = NULL;
						varflag=false;
					}
					
				}
				if(!node_down && vartemp->place_ptr){
				
					tmp_place = vartemp->place_ptr;
					while(tmp_place){
						var = tmp_place->first_trans_node->output_var;
						if(Search_var_from_graph(varsearch,var,prevtr,prevcomp,prev_sig,prev_op,prevout,tmp_state,true,send_value)){
							search = true;
							node_down = true;
							if(send_value) prevtr = tmp_place->first_trans_node;
							break;
						}
						else node_down = false;
						tmp_place = tmp_place->next_place;
					}
					if(!search){
						vartemp=NULL;
						varflag=false;
					}
					
				}
				if(!node_down && vartemp->signal_selector_out){
				
					if(send_value) prev_sig = vartemp->signal_selector_out;
					vartemp = vartemp->signal_selector_out->out_signal;
					node_down = true;
					continue;
				}	
				
				if(!node_down){
					vartemp=NULL;
					varflag=false;
				}
	
			}
			
		if(!search) tmp_state = tmp_state->next_state;
		else tmp_state = NULL;
	}

//if the output is from a comparator or signal_selector only then search is true
if(send_value && (prevcomp || prev_sig)) search = true;

return search;

}



