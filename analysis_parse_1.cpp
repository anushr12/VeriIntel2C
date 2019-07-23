#include <iostream>
#include <new>
#include <stdio.h>
#include <string.h>
/*
#include "/home/anushree1/verific_lib_eval/util/VerificSystem.h"
//#include "/home/anushree1/verific_lib_eval/containers/Array.h"          // Make dynamic array class Array available
//#include "/home/anushree1/verific_lib_eval/containers/Map.h"            // Make associated hash table class Map available
#include "/home/anushree1/verific_lib_eval/util/Strings.h"        // A string utility/wrapper class


//#include "Message.h"        // Make message handlers available, not used in this example

#include "/home/anushree1/verific_lib_eval/verilog/veri_file.h"      // Make Verilog reader available

#include "/home/anushree1/verific_lib_eval/verilog/VeriModule.h"     // Definition of a VeriModule and VeriPrimitive
#include "/home/anushree1/verific_lib_eval/verilog/VeriId.h"         // Definitions of all identifier definition tree nodes
#include "/home/anushree1/verific_lib_eval/verilog/VeriExpression.h" // Definitions of all verilog expression tree nodes
#include "/home/anushree1/verific_lib_eval/verilog/VeriModuleItem.h" // Definitions of all verilog module item tree nodes
#include "/home/anushree1/verific_lib_eval/verilog/VeriStatement.h"  // Definitions of all verilog statement tree nodes
#include "/home/anushree1/verific_lib_eval/verilog/VeriMisc.h"       // Definitions of all extraneous verilog tree nodes (ie. range, path, strength, etc...)
#include "/home/anushree1/verific_lib_eval/verilog/VeriConstVal.h"   // Definitions of parse-tree nodes representing constant values in Verilog.
#include "/home/anushree1/verific_lib_eval/verilog/VeriScope.h"      // Symbol table of locally declared identifiers
#include "/home/anushree1/verific_lib_eval/verilog/VeriLibrary.h"    // Definition of VeriLibrary

#include "analysis_parse.h"
*/

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
#include "analysis_parse.h"
#include "petri_graphTransform.h"
#include "DFG_transform.h"
using namespace std;

#ifdef VERIFIC_NAMESPACE
using namespace Verific ;
#endif

/*Global structure variables declaration*/
ModuleInstantiate *first_module;
Always_block *first_always_node;
DeclareData *first_data_node;
Operate_node *first_operation_node;
ComplexOp_node *first_compoperation_node;
Graph_node *graph_start_node; // the node for a specific module
Graph_node *graph_first_node;
Assign_var *first_var_node;
Assign_const *first_const_node;
State_var *first_state;

extern Place_block *first_place_node;
extern Place_block *first_parallel_place;
extern Equal_to_op *first_EqualTo_node;




int main(int argc, char *argv[]){
  
  veri_file veriReader;
  
  char *file_nm = 0;//"kasumi_E.v";
  char *filename = 0;
  const char *name;
  bool fsmflag = false;
  bool datapathflag=false;
  int x,create=0;
  int transform = 0;
  VeriModule *module;
  MapIter mi;
  DeclareData *tmpn = NULL;
  
  for(x=0;x<argc;x++){
  	if(!strcmp(argv[x],"-filename")){
  	x++;
  	filename = (char *) ::operator new(strlen(argv[x])+1);
  	strcpy(filename , argv[x]);
  	}
  	else if(strstr(argv[x],".v")){
  	file_nm = (char *) ::operator new(strlen(argv[x])+1);
  	strcpy(file_nm,argv[x]);
  	}
  }
  
  
  
    
  //analyze the verilog file into the work library. In case of any error, do not proceed further.

  if(!veriReader.Analyze(file_nm, veri_file::VERILOG_2K)) return 1;
  
  
  
  //Map *all_modules = veriReader.AllModules(); //Get all the modules
  //VeriModule *module;
  //Mapiter mi;
  
  //FOREACH_MAP_ITEM(veri_file::AllModules(),mi, &name, &module){
//  	CreateGraphNodes(module);
//}

  Array *top_mod_array = veriReader.GetTopModules();

 //  VeriModule *module = veriReader.GetModule("filter_dat");
     
  if (!module) {
    // If there is no top level module then issue error
    //  Message::Error(0,"Cannot find any top module. Check for recursive instantiation") ;
    cout<<"\n cannot find top module. check for rcursive instantiation\n";
    return 1 ;
  }
  
 VeriModule *module_first = (VeriModule *)top_mod_array->GetFirst();
 const char *modname = module_first->GetName();
  
 
  
    
FOREACH_MAP_ITEM(veriReader.AllModules(), mi, &name, &module){
  if(strstr(name , "_fsm")){
  //continue; // create function for parsing the fsm and identify the parameter keywords
  Create_state_variables(module);
  fsmflag = true;
  }
  else if(strcmp(name,module_first->GetName())){ //if its not an fsm and not the  top module, then it is a datapath module
  	graph_start_node = new Graph_node;
 	 graph_start_node->name = name;
  	Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,graph_start_node,NULL,NULL);
  	CreateModuleItems(module);
  	Insert_graphnode_list(graph_start_node,false);
  	//datapathflag=true;
  	// -- deleting variable list only if an FSM is detected
  	if( fsmflag && graph_start_node == graph_first_node)
	  	delete_var_list(graph_start_node,tmpn);
  }
 
 	 //fsmflag=false;datapathflag=false;
  }
  
  //then by default take the top module only if there is no FSM or separate datapath
  if(!fsmflag){
  graph_start_node = new Graph_node;
   Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,graph_start_node,NULL,NULL);
  graph_start_node->name = module_first->GetName();
  CreateModuleItems(module_first);
  Insert_graphnode_list(graph_start_node,true);
  //since this is the TOP module, then var_list should be deleted
  delete_var_list(graph_start_node,tmpn);
  
  }
  
   create = create_petri_graph(graph_first_node , first_state);
  
  if(create)
  	transform = Transform_to_flow_graph(first_state,first_place_node,first_parallel_place,first_EqualTo_node);

  
  ::operator delete(filename);
  return 1;
}


void Create_state_variables(VeriModuleItem *module_item){


//ID_VERIDATADECL

//detect if the data type is PARAMETER value is 347
//data_decl->IsParamDecl()
//then declare the variable is a state variable

const char *name = NULL;

switch(module_item->GetClassId()){

case ID_VERIMODULE:
{
	VeriModule *module = static_cast<VeriModule*>(module_item);
	Array *module_items = module->GetModuleItems() ;
	unsigned i;
        VeriModuleItem *module_item ;
        FOREACH_ARRAY_ITEM(module_items, i, module_item) {
            Create_state_variables(module_item) ;
        }
        break;
  }

case ID_VERIDATADECL:

{
	VeriDataDecl *data_decl = static_cast<VeriDataDecl*>(module_item) ;
	// if it is a parameter, declare as a state
	
	if(data_decl->GetDir()==VERI_OUTPUT)
	{
		// put the name of the state variable as DeclareData 
		State_var *new_state = new State_var;
		Initialize_nodes(NULL,NULL,new_state,NULL,NULL,NULL);
		Array *ids = (data_decl) ? data_decl->GetIds() : 0 ;
       	 	VeriIdDef *id_def ;
        	unsigned j ;
        	FOREACH_ARRAY_ITEM(ids,j, id_def){
        	if (!id_def) continue ;
		
		// new_state->state_name = DeclareData variable
		name = id_def->Name();
		new_state->state_name = new DeclareData;
		Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL, new_state->state_name, NULL,NULL,NULL);
		new_state->state_name->name = name;
		Insert_in_state_list(new_state,first_state);
		}
	}
	break;
}

case ID_VERINETDECL:
{

	VeriNetDecl *net_decl = static_cast<VeriNetDecl*>(module_item);
	if(net_decl->GetNetType()==VERI_WIRE){
	State_var *new_state = new State_var;
	Initialize_nodes(NULL,NULL,new_state,NULL,NULL,NULL);
	new_state->signal_selector_out=NULL;
	new_state->next_state=NULL;
	new_state->prev_state=NULL;
	
       	 	VeriIdDef *id_def ;
        	unsigned j ;
        	FOREACH_ARRAY_ITEM(net_decl->GetIds(),j, id_def){
        	if (!id_def) continue ;
		
		// new_state->state_name = DeclareData variable
		name = id_def->Name();
		new_state->state_name = new DeclareData;
		Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL, new_state->state_name, NULL,NULL,NULL);
		new_state->state_name->name = name;
		Insert_in_state_list(new_state,first_state);
		}

	}
	break;		
}	

}
}


void Insert_in_state_list( State_var *state,State_var*& first_state){

State_var *temp = NULL;

if( !first_state){
	first_state= state;
	first_state->next_state = NULL;
	first_state->prev_state = NULL;
	}
else{
	for(temp = first_state; temp->next_state!=NULL; temp = temp->next_state);
	temp->next_state = state;
	state->prev_state = temp;
	state->next_state = NULL;
    }
    
}



static void CreateModuleItems(VeriModuleItem *module_item){

 
      unsigned i;
	first_module = NULL;
      first_always_node=NULL;
      first_data_node=NULL;
      first_operation_node=NULL;
     // graph_start_node=NULL; // the node for a specific module
    //  graph_first_node=NULL;
	first_var_node=NULL;
	first_const_node=NULL;
	
	
      VeriModule *module = static_cast<VeriModule*>(module_item) ;
      Array *module_items = module->GetModuleItems() ;
        VeriModuleItem *module_i;
        FOREACH_ARRAY_ITEM(module_items, i, module_i) {
	if(module_i->GetClassId() == ID_VERIMODULEINSTANTIATION |  ID_VERIDATADECL | ID_VERINETDECL | ID_VERICONTINUOUSASSIGN | ID_VERIALWAYSCONSTRUCT)
	CreateGraphNodes(module_i) ;
        }
        
   }
  
  
  
  void CreateGraphNodes(VeriModuleItem *module_item){
  
  // DeclareData *data_node = NULL;
   bool operator_flag = false;
   bool compop = false;
  
  switch(module_item->GetClassId()){
  
  
  case ID_VERIMODULEINSTANTIATION:
    {
      ModuleInstantiate *module_inst = new ModuleInstantiate; // define the object of the instantiated module structure
      Initialize_values(module_inst, NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);

      VeriModuleInstantiation *mod_inst = static_cast<VeriModuleInstantiation*>(module_item) ;
      // find the ports 
      
      VeriInstId *inst_id;
      unsigned j;
      FOREACH_ARRAY_ITEM(mod_inst->GetIds(), j, inst_id) {
	if (!inst_id) continue ;
	
	Array *port_conn_arr = inst_id->GetPortConnects() ; // Get an array of port connects
	VeriExpression *expr ;
	unsigned k ;
	FOREACH_ARRAY_ITEM(port_conn_arr, k, expr) {
	  VeriPortConnect *port_connect = static_cast<VeriPortConnect*>(expr);
	  VeriExpression *conn = port_connect->GetConnection();
	  VeriIdRef *id_ref = (VeriIdRef *)conn;
	  const char *port_name = id_ref->GetName();
	  VeriIdDef *id_def = id_ref->FullId();
	  DeclareData *new_node = new DeclareData;
	  insert_port_list(port_name, module_inst, new_node,NULL,false,true);
	  
	  //  insert_port_list(port_name, module_inst,new_node,false);
	  //put this port name into outputs list
	    }  
      }

	module_inst->mod_name = mod_inst->GetModuleName();
	//module_inst->optype = mod_inst->Get
	insert_moduleInst_list(module_inst); //insert the instantiated module in the list of the instantiated modules
	graph_start_node->module_inst_node = first_module; //connect the first instantiated module to the graph node
	//delete module_inst;
	break;
    }
    
  case ID_VERINETDECL:
  
  case ID_VERIDATADECL:
    {
      // declare the DeclareData struct pointer
      DeclareData *data_node = new DeclareData;
      Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL, data_node,NULL,NULL,NULL);
      
      
      VeriDataDecl *data_decl = static_cast<VeriDataDecl*>(module_item);
      Array *ids = (data_decl)? data_decl->GetIds():0;
      VeriIdDef *id_def;
      unsigned j;
      FOREACH_ARRAY_ITEM(ids, j, id_def){
	if(!id_def) continue;
	data_node->name = id_def->GetName();
	if(id_def->IsArray()){
	 // VeriRange *dim = id_def->GetDimensions();
	  VeriNetDecl *net_decl = static_cast<VeriNetDecl *>(module_item);
	  VeriRange *range = net_decl->GetRange();
	  VeriIntVal *int_value = static_cast<VeriIntVal*>(range->GetLeft());
	  
	  data_node->bit_width = (int_value->GetNum())+1;
	}
	  //EDITING HERE FIRST!!!!!
	else if(id_def->IsReg())
	  data_node->data_type = reg;
	else if(id_def->IsVar())
	  data_node->data_type = var;
	else if(id_def->IsNet())
	   data_node->data_type = wire;
	if(id_def->IsInput())
		data_node->data_type = input;

	data_node->array = false;
	data_node->dimensions = 0;
	data_node->bit_width = 0;
	
	insert_datanode_list(data_node);
	graph_start_node->data_node = first_data_node;
      }
      
     // delete data_node;
     // data_node = NULL;
      break;
    }
	
    case ID_VERICONTINUOUSASSIGN:
      {
	unsigned j;
	unsigned op_type;
	const char *net_name = NULL;
	const char *val_name = NULL;
	///////for binary operator case
	const char *left_opname = NULL;
	const char *const_val = NULL;
	const char *right_opname = NULL;
	Assign_var *assign_var_node=NULL;
	Assign_const *assign_const_node = NULL;
	Operate_node *oper_node = NULL;
	Ifthenelse_block *condexpr=NULL;
	//ComplexOp_node *complex_op=NULL;
	DeclareData *leftop , *rightop=NULL;
	unsigned oper_type;
	bool condflag=false;
	
	int iternum=0;
	/////end of the declarations
	
	VeriContinuousAssign *cont_assign = static_cast<VeriContinuousAssign*>(module_item) ;
	Array *net_assign_arr = cont_assign->GetNetAssigns();
	VeriNetRegAssign *net_reg_assign;
	 FOREACH_ARRAY_ITEM(net_assign_arr,j,net_reg_assign){
	   
	   VeriExpression *lval = net_reg_assign->GetLValExpr();
	   VeriExpression *rval = net_reg_assign->GetRValExpr();
	   VeriIdRef *id_ref = (VeriIdRef *)lval;
	   net_name  = id_ref->GetName();
	   
	  
	   if(rval->GetClassId() == ID_VERIIDREF){
	     assign_var_node= new Assign_var;
	     Initialize_values(NULL, NULL,NULL,assign_var_node,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
	     assign_const_node = NULL;
	     id_ref = (VeriIdRef *)rval;
	     val_name = id_ref->GetName(); // right expr
	    	    
	    
	   }
	   else if(rval->GetClassId() == ID_VERICONSTVAL){
	     assign_var_node=NULL;
	     assign_const_node = new Assign_const;
	     Initialize_values(NULL, NULL,NULL,NULL,assign_const_node,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
	     //assign_const_node = (Assign_const *)malloc(sizeof(Assign_const));
	   //  net_name = id_ref->GetName();//left expr
	     VeriConstVal *constant_value = static_cast<VeriConstVal*>(rval);
	     assign_const_node->const_expr = constant_value->Image(); //right expr
	     assign_const_node->const_value = constant_value->Integer();
	      VeriExpression *lval = net_reg_assign->GetLValExpr();
	      id_ref = (VeriIdRef *)lval;
	    
	      val_name = NULL;
	   }
	
	   else if(rval->GetClassId() == ID_VERIUNARYOPERATOR){
	   	VeriUnaryOperator * un_op = static_cast<VeriUnaryOperator*>(rval) ;
		VeriExpression *arg_expr = un_op->GetArg();
		oper_type = un_op->OperType();
		
		if(arg_expr->GetClassId() == ID_VERIIDREF){
	 	    	VeriIdRef *idref = (VeriIdRef*)arg_expr;
	     		assign_var_node= new Assign_var;
	     		Initialize_values(NULL, NULL,NULL,assign_var_node,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
	     		assign_const_node = NULL;
	     		val_name = idref->GetName(); // right expr
	     	}
	      // this will be an ifthenelse block ( if its an unary operator, and then a binary operation, this indicates ifthenelse)
	      //if there is in_control_operation, then there is no ifcondition_var.
	     	else if(arg_expr->GetClassId()==ID_VERIBINARYOPERATOR){
	     
		     	condflag = true; //to indicate condexpr is built
		     	condexpr = new Ifthenelse_block;
			Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,condexpr,NULL,NULL,NULL,NULL,NULL);
		     	condexpr->in_control_operation = new Operate_node;
		     	Initialize_values(NULL, NULL,condexpr->in_control_operation,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
		     	condexpr->in_control_operation->input_list = new PortList;
		     	Initialize_values(NULL, condexpr->in_control_operation->input_list,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
		     	
		     	VeriBinaryOperator *bin_op = static_cast<VeriBinaryOperator*>(arg_expr) ;
			     //	oper_node->operator_type = bin_op->OperType(); //unsigned token for the operator
		     //	op_type = bin_op->OperType();
			VeriExpression *left = bin_op->GetLeft(); //left expr of the binary operation
			
			if(left->GetClassId() == ID_VERIIDREF){
				VeriIdRef *id = (VeriIdRef*)left;
				left_opname = id->GetName();
				//condexpr->if_condition_var = new DeclareData;
				//Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,condexpr->if_condition_var,NULL,NULL,NULL);
				//condexpr->if_condition_var->name = left_opname;
				DeclareData *node = new DeclareData;
				Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,node,NULL,NULL,NULL);
				node->name = left_opname;
				insert_in_list(condexpr->in_control_operation->input_list,node);
				
			}
				
		     	VeriExpression *right = bin_op->GetRight(); //right expr of the binary operation
		     	if(right->GetClassId() == ID_VERICONSTVAL){
		     		VeriConstVal *cval = static_cast<VeriConstVal*>(right);
		     		const_val = cval->Image();
		     		condexpr->equal_condition = new Assign_const;
		     		Initialize_values(NULL, NULL,NULL,NULL,condexpr->equal_condition,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
				condexpr->equal_condition->left_value = new DeclareData;
				Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,condexpr->equal_condition->left_value,NULL,NULL,NULL);
				condexpr->equal_condition->left_value->name = left_opname;
		     		condexpr->equal_condition->const_expr = const_val;
		     		//if there is equal_condition, then only then_var exists
		     		condexpr->then_var = new DeclareData;
		     		Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,condexpr->then_var,NULL,NULL,NULL);
		     		condexpr->then_var->name = net_name;
		     		
	     		
	     		}
		     	else if(right->GetClassId() == ID_VERIIDREF){
	     			VeriIdRef *id = (VeriIdRef*)right;
	     			right_opname = id->GetName();
	     			//condexpr->if_condition_var = new DeclareData;
	     			//Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,condexpr->if_condition_var,NULL,NULL,NULL);
	     			//condexpr->if_condition_var->name = right_opname;
	     			DeclareData *node = new DeclareData;
				Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,node,NULL,NULL,NULL);
				node->name = right_opname;
				insert_in_list(condexpr->in_control_operation->input_list,node);
	     			//CHANGED HERE
	  		
	 	    	}
	 	    	else if(right->GetClassId() == ID_VERIINDEXEDID){
	 	    		VeriIndexedId *indexedid = static_cast<VeriIndexedId*>(right);
	 	    		right_opname = indexedid->GetName();
	 	    		DeclareData *node = new DeclareData;
				Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,node,NULL,NULL,NULL);
				node->name = right_opname;
				insert_in_list(condexpr->in_control_operation->input_list,node);
	 	    	}
	 	    	//to attach the output of condexpr if its not attached
	 	    	if(!condexpr->then_var){
	 	    		condexpr->then_var = new DeclareData;
	 	    		Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,condexpr->then_var,NULL,NULL,NULL);
		     		condexpr->then_var->name = net_name;
	 	    	}
	     	//CHANGED HERE
	   	  	//condexpr->then_expr_var->left_value = new DeclareData;
	     		//Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,condexpr->then_expr_var->left_value,NULL,NULL,NULL);
	     		//condexpr->then_expr_var->left_value->name = net_name;
	 	
	     	}
	     	
	     }
	     //EDITING HERE FIRST!!!
	     else if(rval->GetClassId() == ID_VERIBINARYOPERATOR){ //right expression if it consists of operation node
	     	oper_node = new Operate_node;
	     	Initialize_values(NULL, NULL,oper_node,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
	     	oper_node->input_list = new PortList;
	     	 Initialize_values(NULL, oper_node->input_list,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
	     	VeriBinaryOperator *bin_op = static_cast<VeriBinaryOperator*>(rval) ;
	     	oper_node->operator_type = bin_op->OperType(); //unsigned token for the operator
	     	op_type = bin_op->OperType();
		VeriExpression *left = bin_op->GetLeft(); //left expr of the binary operation
		
		if(left->GetClassId()==ID_VERIUNARYOPERATOR){
			VeriUnaryOperator * un_op = static_cast<VeriUnaryOperator*>(left) ;
			VeriExpression *arg_expr = un_op->GetArg();
			VeriIdRef *idref = (VeriIdRef*)arg_expr;
	     		left_opname = idref->GetName();
		}
		else if(left->GetClassId()==ID_VERIIDREF){
			VeriIdRef *id = (VeriIdRef*)left;
			left_opname = id->GetName();
		}
		else if(left->GetClassId() == ID_VERICONCAT){
			VeriConcat *concat = static_cast<VeriConcat*>(left);
			Array *expr_arr = concat->GetExpressions();
			unsigned i;
			VeriExpression *expr;
			FOREACH_ARRAY_ITEM(expr_arr,i,expr){
				if(expr->GetClassId() == ID_VERIIDREF){
					VeriIdRef *idref = (VeriIdRef*)expr;
					left_opname = idref->GetName();
				}
			}
		
		}
		
		//if there is a binary complex operation inside one binary operation, then all the inputs must be collected in the inputlist of the operation node
		else CreateComplexOperations(left,condexpr,true,0,true,iternum,oper_node);
		
		
		VeriExpression *right = bin_op->GetRight(); //right expr of the binary operation
	     	if(right->GetClassId() == ID_VERICONSTVAL){
	     		VeriConstVal *cval = static_cast<VeriConstVal*>(right);
	     		const_val = cval->Image();
	     		DeclareData *node = new DeclareData;
	     		Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,node,NULL,NULL,NULL);
	     		node->name = const_val;
	     		node->data_type = integer;
	     		node->array = false;
	     		
	     		insert_in_list(oper_node->input_list , node);
	     		//delete node;
	     		}
	     	else if(right->GetClassId() == ID_VERIIDREF){
	     		VeriIdRef *id = (VeriIdRef*)right;
	     		right_opname = id->GetName();
	     		}
	     		
	     	else if(right->GetClassId() == ID_VERIUNARYOPERATOR){
	     		VeriUnaryOperator * un_op = static_cast<VeriUnaryOperator*>(right) ;
			VeriExpression *arg_expr = un_op->GetArg();
			
		
			VeriIdRef *idref = (VeriIdRef*)arg_expr;
	     		right_opname = idref->GetName();
	     		
			
			if(arg_expr->GetClassId() == ID_VERIBINARYOPERATOR){
				//TO BE DONE HERE!!
				
				VeriBinaryOperator *bin_op = static_cast<VeriBinaryOperator*>(arg_expr) ;	
				
				VeriExpression *left = bin_op->GetLeft();
				if(left->GetClassId()==ID_VERIIDREF){
					VeriIdRef *id = (VeriIdRef*)left;
					leftop = new DeclareData;
					Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,leftop,NULL,NULL,NULL);
					leftop->name = id->GetName();
					insert_in_list(oper_node->input_list,leftop);
				}
				else if(left->GetClassId()==ID_VERICONSTVAL){
					VeriConstVal *constant_value = static_cast<VeriConstVal*>(left);
					leftop = new DeclareData;
					Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,leftop,NULL,NULL,NULL);
					leftop->name = constant_value->Image();
					leftop->data_type = integer;
					insert_in_list(oper_node->input_list,leftop);
				}
				
				VeriExpression *right = bin_op->GetRight();
				
				//right value of the operation
				if(right->GetClassId()==ID_VERIIDREF){
					VeriIdRef *id = (VeriIdRef*)right;
					rightop = new DeclareData;
					Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,rightop,NULL,NULL,NULL);
					rightop->name = id->GetName();
					insert_in_list(oper_node->input_list,rightop);
				}
				else if(right->GetClassId()==ID_VERICONSTVAL){
					VeriConstVal *constant_value = static_cast<VeriConstVal*>(right);
					rightop = new DeclareData;
					Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,rightop,NULL,NULL,NULL);
					rightop->name = constant_value->Image();
					rightop->data_type = integer;
					insert_in_list(oper_node->input_list,rightop);
				}
				//compop = true;
				
				 //CreateComplexOperations( complex_op , 
	     		}
	     		
	     	}
	     	else if(right->GetClassId() == ID_VERIINDEXEDID){
	     		VeriIndexedId *indexedid = static_cast<VeriIndexedId*>(right);
	     		right_opname = indexedid->GetName();
	     	}
	     	
	     	else CreateComplexOperations(right,condexpr,true,0,true,iternum,oper_node);
	     		
	        operator_flag = true;
	        
	     	}
	     	else if(rval->GetClassId() == ID_VERIINDEXEDID){
	     		assign_var_node= new Assign_var;
	  	        Initialize_values(NULL, NULL,NULL,assign_var_node,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
		        assign_const_node = NULL;
	     		VeriIndexedId *indexedid = static_cast<VeriIndexedId*>(rval);
	     		val_name = indexedid->GetName();
	     	}
	     	
	     // now search for these names and put in the operation node!!!!!
	     
	     
	   DeclareData *d_node=NULL;
	   bool checkr=false, checkl=false;
	   
	   // check if the rval is a constant or variable, then declare Assign_var or Assign_const node accordingly.
	  

	   	  
	   //search for this declare data node in the list of DeclareData or operation node as decided above
	   if(!condflag){
		   for(d_node = first_data_node ; d_node!= NULL;d_node = d_node->next_n){
		   	if(Search_var_InStateList(d_node,first_state))
		   		d_node->data_type = var;
		   		
		     if(d_node->name == net_name){ //left expr
		        if(assign_var_node && !assign_const_node){
		          assign_var_node->left_value = new DeclareData;
			  assign_value(assign_var_node->left_value , d_node);
			  }
			else if(assign_const_node && !assign_var_node){
			  assign_const_node->left_value = new DeclareData;
			  assign_value(assign_const_node->left_value , d_node);
			  }
			else if(operator_flag == true){
				  oper_node->output = new DeclareData;
				  assign_value(oper_node->output,d_node);
			  }
			/* else if(compop == true){
			 	complex_op->out_value = new DeclareData;
			 	assign_value(complex_op->out_value , d_node);
			 }*/
		checkl = true;
	      
	 	    }
		     else if((d_node->name == left_opname || d_node->name == right_opname) && operator_flag==true){ //check if it is binary operator type
			     DeclareData *node=new DeclareData;
			     assign_value(node , d_node);
			  /*   if(!oper_node->input_list) {
			     oper_node->input_list = new PortList;
			      Initialize_values(NULL, oper_node->input_list,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
			      }
			     */
		   	  insert_in_list(oper_node->input_list,node);
	     //delete node;
		     }
	    
	     
		     else if(val_name && d_node->name == val_name){ //right expr
		 	      if(assign_var_node && !assign_const_node){
	        		 assign_var_node->right_value = new DeclareData;
				 assign_value(assign_var_node->right_value, d_node);
				 if(rval->GetClassId() == ID_VERIUNARYOPERATOR)
					 assign_var_node->right_value->unary_operator = oper_type;
			}
	       
	       checkr = true;
	     }
	     if(checkl && checkr)
	       break;
	     else
	       continue;
	   }
	  }
	 }
	 //insert this in the varassign list??
	 //insert the operation node in its list
	 if(operator_flag == true){
	 	 insert_operation_list(oper_node , NULL,graph_start_node);
	 	 graph_start_node->operation_node = first_operation_node;
	 	
	 	}
	/* else if(compop){
	 	insert_operation_list(NULL , complex_op);
	 	graph_start_node->complexop_node = first_compoperation_node;
	 }*/
	 	
	 else if(assign_var_node && !assign_const_node){
	 	
	 	 
	 	insert_assign_list(assign_var_node , NULL);
	 	graph_start_node->varassign_node = first_var_node;
	 }
	 else if(assign_const_node && !assign_var_node){
	 	
	 	insert_assign_list(NULL, assign_const_node);
	 	graph_start_node->constassign_node = first_const_node;
	 	
	 }
	 else if(condflag){
	 	insert_cond_list(condexpr,graph_start_node);
	 	
	 }
	 //delete assign_var_node; assign_var_node = NULL;
	// delete assign_const_node; assign_const_node = NULL;
	 //delete oper_node; oper_node = NULL;
	 break;
	 }
	 case ID_VERIALWAYSCONSTRUCT:
	 {
	 VeriExpression *expr;
	 unsigned j;
	 bool checkforcond = false;
	 bool seqflag = false; //to check if there are two sequential blocking assign statements
	 Always_block *always_node = new Always_block;
	 Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,always_node,NULL,NULL,NULL,NULL);
	 VeriAlwaysConstruct *always_stmt = static_cast<VeriAlwaysConstruct*>(module_item);
	 VeriStatement *stm = always_stmt->GetStmt();
	 VeriEventControlStatement *event_control = static_cast<VeriEventControlStatement*>(stm); //to get the handle of the event control
	 Array *ids = event_control->GetAt();
	 always_node->event_controls = new PortList;
	  Initialize_values(NULL, always_node->event_controls,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
	 // We need to check if any of the event conditions are RESET or CLOCK, then avoid this always block, it is not needed for our operation
	 FOREACH_ARRAY_ITEM(ids,j, expr){
	 	VeriEventExpression *evt_expr = static_cast<VeriEventExpression*>(expr);
	 	expr = evt_expr->GetExpr();
	 	VeriIdRef *id_ref = (VeriIdRef*)expr;
	 	const char *name = id_ref->GetName();
	 	if(strcmp(name , "CLOCK")==0 || strcmp(name, "RESET")==0){
	 		// put the flag
	 		//checkforcond = true;
	 		delete always_node->event_controls;
	 		always_node->event_controls = NULL;
	 		break;
	 		}
	 		else{
	 	// Store the event control variables in the portlist structure 
	 			if(event_control->GetStmt()->GetClassId() == ID_VERICASESTATEMENT)
	 				break;
	 			DeclareData *node = new DeclareData;
	 			 Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,node,NULL,NULL,NULL);
	 			node->name = id_ref->GetName();
	 			insert_in_list(always_node->event_controls , node);
	 		}
	 	
	 }
	 
	 	 VeriStatement *event_stmt = event_control->GetStmt() ;
	 	 CreateNodesInAlwaysBlock(event_stmt, always_node,false,seqflag); //to create the node under the always block
	 	if(always_node->event_controls && !always_node->event_controls->first_port)
			Insert_event_controls(always_node);
	 	 // insert the always node in the list of always node
	 	 if(!seqflag)
		 	 Insert_in_always_list(always_node);
	 
	 graph_start_node->always_node = first_always_node;
	 //delete always_node;
	 break;
	 } //end of the always case
	 
	 	  
	 } //end of switch statement
	 
	
	 
      
  }

	
void insert_port_list(const char *pname , ModuleInstantiate *inst, DeclareData *in_node,Func_opmodule *opmod,bool flag,bool portorinout){

  DeclareData *data_n=NULL;

  for(data_n = first_data_node ; data_n!= NULL; data_n = data_n->next_n){
    if( data_n->name == pname){
      
 	     assign_value(in_node , data_n);
      		break;
      }
    
  }

if(portorinout == true){
	if( inst->ports_list == NULL){
		PortList *p_list = new PortList;
		 Initialize_values(NULL, p_list,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
		inst->ports_list = p_list;
		inst->ports_list->first_port = in_node;
		}
	else
	insert_in_list(inst->ports_list , in_node);
	}
	
else{
  if(flag == true){
  if(opmod->input_list == NULL){
    
    PortList *inlist = new PortList;
     Initialize_values(NULL, inlist,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
    opmod->input_list = inlist;
    (opmod->input_list)->first_port = in_node;
  }
  else 
    insert_in_list(opmod->input_list , in_node);
  }

  else if(flag == false){
    if(opmod->output_list == NULL){
      
      PortList *outlist = new PortList;
       Initialize_values(NULL, outlist,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
      opmod->output_list = outlist;
      (opmod->output_list)->first_port = in_node;
    }
    else 
      insert_in_list(opmod->output_list , in_node);
  }
}
 data_n = NULL;
}

// insert the nodes in the port list , input or output list or ports of a module or operation node
void insert_in_list(PortList *list, DeclareData *node){
  
  DeclareData *data_n=NULL;
  
  if( list->first_port == NULL){
    list->first_port = node;
    node->next_n = NULL;
    node->prev_n = NULL;
  }
  else{
    for(data_n = list->first_port; data_n->next_n!=NULL; data_n = data_n->next_n);
    data_n->next_n = node;
    node->prev_n = data_n;
    node->next_n = NULL;
  }
 
 data_n = NULL;
}

void insert_moduleInst_list(ModuleInstantiate *list){

  ModuleInstantiate *ln;

  if(first_module == NULL){
    first_module = list;
    list->nextm = NULL;
    list->prevm = NULL;
  }

  else{
    for(ln = first_module ; ln->nextm != NULL; ln = ln->nextm);
    ln->nextm = list;
    list->prevm = ln;
    list->nextm = NULL;
  }

}

void insert_datanode_list( DeclareData *newnode){

  DeclareData *tmp = NULL;

  if(first_data_node == NULL){
    first_data_node = newnode;
    newnode->prev_n = NULL;
    newnode->next_n = NULL;
   // graph_start_node->data_node = first_data_node;
  }

  else{
    for( tmp = first_data_node ; tmp->next_n != NULL; tmp = tmp->next_n);
    tmp->next_n = newnode;
    newnode->prev_n = tmp;
    newnode->next_n = NULL;
  }
}

// insert the operation node in the list of the operations only for continuous assign block (not for always block)
void insert_operation_list(Operate_node *op_node , ComplexOp_node *compop_node,Graph_node *graph_start_node){

Operate_node *tmp = NULL;
ComplexOp_node *tmpc = NULL;

if(op_node){	
	if(graph_start_node->operation_node == NULL){
		graph_start_node->operation_node = op_node;
		first_operation_node = op_node;
		op_node->next_op = NULL;
		op_node->prev_op = NULL;
	}
		
	else{
		for(tmp = graph_start_node->operation_node ; tmp->next_op!=NULL; tmp = tmp->next_op);
		tmp->next_op = op_node;
		op_node->prev_op = tmp;
		op_node->next_op = NULL;
	}
}

else if(compop_node){
	if(first_compoperation_node == NULL){
		first_compoperation_node = compop_node;
		compop_node->next_op = NULL;
		compop_node->prev_op = NULL;
		}
		
	else{
		for(tmpc = first_compoperation_node ; tmpc->next_op!=NULL; tmpc = tmpc->next_op);
		tmpc->next_op = compop_node;
		compop_node->prev_op = tmpc;
		compop_node->next_op = NULL;
		}

}
}



void Insert_in_always_list(Always_block *node){

Always_block *tmp = NULL;

if(first_always_node == NULL){

	first_always_node = node;
	first_always_node->prev_n = NULL;
	first_always_node->next_n = NULL;
	}
	else{
	for(tmp = first_always_node;tmp->next_n!=NULL;tmp = tmp->next_n);
	tmp->next_n = node;
	node->prev_n = tmp;
	node->next_n = NULL;
	}
}


void insert_assign_list( Assign_var *v_node, Assign_const *c_node){

Assign_var *tmpv = NULL;
Assign_const *tmpc = NULL;
if(v_node){
	if(first_var_node == NULL){
	first_var_node = v_node;
	v_node->next_n = NULL;
	v_node->prev_n = NULL;
	}
	else{
	for(tmpv = first_var_node;tmpv->next_n!=NULL; tmpv = tmpv->next_n);
	tmpv->next_n = v_node;
	v_node->prev_n = tmpv;
	v_node->next_n = NULL;
	}
}
else if(c_node){
	if(first_const_node == NULL){
	first_const_node = c_node;
	c_node->next_n = NULL;
	c_node->prev_n = NULL;
	}
	else{
	for(tmpc = first_const_node;tmpc->next_n!=NULL; tmpc = tmpc->next_n);
	tmpc->next_n = c_node;
	c_node->prev_n = tmpc;
	c_node->next_n = NULL;
	}
}
}


//insertcheck is to indicate if the node should be inserted in the beginning or in the end
void Insert_graphnode_list(Graph_node *node,bool insertcheck){

Graph_node *tmp = NULL;
if(!insertcheck){
	if(graph_first_node == NULL){
		graph_first_node = node;
		node->prev_node = NULL;
		node->next_node = NULL;
	}
	else{
		for(tmp = graph_first_node ; tmp->next_node !=NULL; tmp=tmp->next_node);
			tmp->next_node = node;
			node->prev_node = tmp;
			node->next_node = NULL;
	}
}
else{
	if(graph_first_node == NULL){
		graph_first_node = node;
		node->prev_node = NULL;
		node->next_node = NULL;
	}
	else{
		node->prev_node = NULL;
		graph_first_node->prev_node = node;
		node->next_node = graph_first_node;
		graph_first_node = node;
		
	}


}
	
}
	
//function to insert the conditional node in conditionallist of the graph node
void insert_cond_list(Ifthenelse_block *expr,Graph_node *graph_n){

Ifthenelse_block *tmp=NULL;

if(!graph_n->ifthenelse_node){
	graph_n->ifthenelse_node = expr;

}
else{
	for(tmp = graph_n->ifthenelse_node ; tmp->next_block!=NULL;tmp = tmp->next_block);
		tmp->next_block=expr;
		expr->next_block=NULL;
}
	

}



		

//copy the data of the variables in the node2 to node1
void assign_value( DeclareData *node1 , DeclareData *node2){

  node1->bit_width = node2->bit_width;
  node1->array = node2->array;
  node1->name = node2->name;
  node1->data_type = node2->data_type;
  node1->dimensions = node2->dimensions;
  node1->next_n = NULL;
  node1->prev_n = NULL;
  node1->unary_operator = 0;
  node1->operator_out=NULL;
  node1->operator_in=NULL;
  node1->equal_op_out=NULL;
  node1->comparator_out=NULL;
  node1->signal_selector_out = NULL;
  node1->transition_out=NULL;
  node1->place_ptr=NULL;
  node1->dfgnode_out=NULL;
  
}


void Initialize_values( ModuleInstantiate *node1,PortList *node2,Operate_node *node3,Assign_var *node4,Assign_const *node5,Case_Statement *node6,Ifthenelse_block *node7,Always_block *node8 , DeclareData *node9, Graph_node *node10 , ComplexOp_node *node11 , Transition_block *node12){

if(node1){
	node1->mod_name = NULL;
	node1->optype = '\0';
	node1->ports_list = NULL;
	//node1->output_list = NULL;
	node1->nextm = NULL;
	node1->prevm = NULL;
	}
else if(node2){
	node2->next_p = NULL;
	node2->prev_p = NULL;
	//node2->port_name = NULL;
	node2->first_port=NULL;
	}
else if(node3){
	node3->input_list=NULL;
        node3->output=NULL;
        node3->operator_type=0;
        node3->prev_op=NULL;
        node3->next_op=NULL;
        }
else if(node4){
	node4->left_value = NULL;
	node4->right_value = NULL;
	//node4->operation_rhs = NULL;
	node4->next_n = NULL;
	node4->prev_n = NULL;
	}
else if(node5){
	node5->left_value = NULL;
	node5->const_value = 0;
	node5->const_expr = NULL;
	node5->prev_n = NULL;
	node5->next_n = NULL;
	}
	
else if(node6){
	node6->condition_var = NULL;
	node6->case_value = 0;
	node6->expression_ct = NULL;
	node6->expression_vt = NULL;
	node6->next_n = NULL;
	node6->prev_n = NULL;
	}
else if(node7){
	node7->if_condition_var=NULL;
        node7->then_expr_var=NULL;
        node7->in_control_operation=NULL;
        node7->equal_condition=NULL;
        node7->else_expr_block=NULL;
        node7->next_block=NULL;
        node7->prev_block=NULL;
        node7->then_var=NULL;
        }
else if(node8){
	node8->event_controls=NULL;
        node8->CaseBlock=NULL;
        node8->CondBlock=NULL;
        node8->assign_expr=NULL;
        node8->operate_expr=NULL;
        node8->prev_n=NULL;
        node8->next_n=NULL;
        }
else if(node9){
	node9->bit_width = 0;
	node9->array = false;
	node9->data_type = var;
	node9->name = NULL;
	//node9->next_operator_out = false;
	//node9->next_selector_out=false;
	node9->dimensions = 0;
	node9->unary_operator = 0;
	node9->operator_out = NULL;
	node9->signal_selector_out=NULL;
	node9->operator_in = NULL;
	node9->equal_op_out = NULL;
	node9->comparator_out = NULL;
	node9->transition_out=NULL;
	node9->place_ptr = NULL;
	node9->dfgnode_out=NULL;
	node9->prev_n = NULL;
	node9->next_n = NULL;
	}
else if(node10){
	//node10->first_node=NULL;
        node10->prev_node=NULL;
        node10->next_node=NULL;
        node10->data_node=NULL;
        node10->ifthenelse_node=NULL;
        node10->varassign_node=NULL;
        node10->constassign_node=NULL;
        node10->always_node=NULL;
        //node10->case_node=NULL;
        node10->operation_node=NULL;
        //node10->complexop_node=NULL;
        node10->module_inst_node=NULL;
        }
else if(node11){
	node11->basic_op1 = NULL;
	node11->basic_op2 = NULL;
	node11->basic_operand = NULL;
	node11->out_value = NULL;
	node11->operator_type = 0;
	node11->prev_op=NULL;
	node11->next_op=NULL;
	}
else if(node12){
	node12->own_place_ptr = NULL;
	node12->outgoing_external_place = NULL;
	node12->outgoing_external_dfg = NULL;
	node12->traverse_node = false;
	node12->output_var = NULL;
	node12->next_trans_node = NULL;
	node12->prev_trans_node=NULL;
	}
}



static void CreateNodesInAlwaysBlock(VeriStatement *statement, Always_block *al_node , bool elseifflag,bool& seqflag){


int iter=0;
Operate_node *operation=NULL;
DeclareData *tmpnode = NULL;
//ComplexOp_node *compexpr=NULL;
Ifthenelse_block *condblock=NULL;
const char *tempname = NULL;

	if(!statement) return;
	
	switch(statement->GetClassId()){
	
	case ID_VERICONDITIONALSTATEMENT:
	{
		//only else statement is required
		//this is for the asynchronous reset nodes
		VeriConditionalStatement *if_stmt = static_cast<VeriConditionalStatement*>(statement) ;
		VeriExpression *if_expr = if_stmt->GetIfExpr();
		VeriIdRef *id_ref = (VeriIdRef*)if_expr;
		tempname = id_ref->GetName(); 
		//CHANGED HERE
		if(!strcmp(tempname,"CLOCK")|| !strcmp(tempname,"RESET")){
			elseifflag = false;
		}
		else elseifflag = true;
		
		if(elseifflag == true){
			Ifthenelse_block *condnode = new Ifthenelse_block;
			Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,condnode,NULL,NULL ,NULL,NULL,NULL);
			VeriExpression *if_expr = if_stmt->GetIfExpr();
			VeriIdRef *id_ref = (VeriIdRef*)if_expr;
			condnode->if_condition_var = new DeclareData;
			Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,condnode->if_condition_var ,NULL,NULL,NULL);
			condnode->if_condition_var->name = id_ref->GetName();
			al_node->CondBlock = condnode;
			if(!al_node->event_controls){
				al_node->event_controls = new PortList;
				Initialize_values(NULL, al_node->event_controls,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
			}
			
			VeriStatement *then_stmt = if_stmt->GetThenStmt();
			CreateNodesInAlwaysBlock(then_stmt , al_node , true,seqflag);
		}
		
		VeriStatement *else_stmt = if_stmt->GetElseStmt() ;
		
		if(else_stmt){	
			if(else_stmt->GetClassId() == ID_VERICONDITIONALSTATEMENT){
				elseifflag = true;
				CreateNodesInAlwaysBlock(else_stmt , al_node , true,seqflag);	
			}
			else
			CreateNodesInAlwaysBlock(else_stmt , al_node , false,seqflag);
			
		}
	break;
	}
	
	case ID_VERINONBLOCKINGASSIGN:
	{
		Assign_var *var_node = new Assign_var; // does not matter if its blocking or non blocking, its assignment expression here
		Initialize_values(NULL, NULL,NULL,var_node,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
		
		VeriNonBlockingAssign *nonblocking_stmt = static_cast<VeriNonBlockingAssign*>(statement) ;
		VeriExpression *lval = nonblocking_stmt->GetLVal();
		VeriIdRef *id = (VeriIdRef*)lval;
		const char *leftname = id->GetName(); //left value
		VeriExpression *val = nonblocking_stmt->GetValue() ; // Gets the right value
		id = (VeriIdRef*)val;
		const char *rightname = id->GetName(); //right name
		
		// attach to the datanodes
		DeclareData *node = NULL;
		for(node = first_data_node; node!=NULL; node = node->next_n){
			if(node->name == leftname){
			var_node->left_value = new DeclareData;
			assign_value(var_node->left_value , node);
			}
			else if(node->name == rightname){
			var_node->right_value = new DeclareData;
			assign_value(var_node->right_value , node);
			}
		}
		if(elseifflag == false)
			al_node->assign_expr = var_node;
		else
			al_node->CondBlock->then_expr_var = var_node;
		break;
		
	}
	case ID_VERICASESTATEMENT:
	{
		//declarations firstly
		const char *val_name = NULL;
		const char *net_name = NULL;
		const char *name = NULL;
		bool checkl = NULL,checkr=NULL;
		
		// attach this case statement node to the always block node
		//al_node->CaseBlock = case_expr;
		Case_Statement *case_expr = new Case_Statement; // graph structure creation of the first case node which has the condition variable
		Initialize_values(NULL, NULL,NULL,NULL,NULL,case_expr,NULL,NULL,NULL,NULL,NULL,NULL);
		
		VeriCaseStatement *casestm = static_cast<VeriCaseStatement*>(statement);
		
		VeriExpression *condition = casestm->GetCondition();
		if(condition->GetClassId() == ID_VERIIDREF){
			VeriIdRef *id_ref = (VeriIdRef*)condition; //Verific data structure
			name = id_ref->GetName();
		}
		else if(condition->GetClassId() == ID_VERIINDEXEDID){
			VeriIndexedId *id = static_cast<VeriIndexedId*>(condition);
			name = id->GetName();
		}
		
		DeclareData *t_node=NULL;
		
		// this is the first case node having only condition info
		if(al_node->CaseBlock == NULL){
			
			for(t_node=first_data_node ; t_node!= NULL; t_node = t_node->next_n){
				if(t_node->name == name){
				case_expr->condition_var = new DeclareData;
				assign_value(case_expr->condition_var , t_node);
				break;
				}
			}
			if(al_node->event_controls){
				al_node->event_controls->first_port = new DeclareData;
				assign_value(al_node->event_controls->first_port , case_expr->condition_var);
			}
			t_node = NULL;
			case_expr->prev_n = NULL;
			case_expr->next_n = NULL;
			al_node->CaseBlock = case_expr;
			//delete the event controls list
			//Delete_list(al_node->event_controls , case_expr->condition_var);
		
		}
		
		case_expr = NULL;	

	// now the creation of the rest of the case items
		Array *items = casestm->GetCaseItems();
		unsigned i;
		VeriCaseItem *item;
		
		FOREACH_ARRAY_ITEM(items,i,item){
			Case_Statement *case_exprn = new Case_Statement; // graph structure creation
			Initialize_values(NULL, NULL,NULL,NULL,NULL,case_exprn,NULL,NULL,NULL,NULL,NULL,NULL);
			Array *conditions = item->GetConditions() ;		
			VeriExpression *condition;
			unsigned j;
			FOREACH_ARRAY_ITEM(conditions, j, condition){
			
			VeriConstVal *const_value = static_cast<VeriConstVal*>(condition);
			case_exprn->case_value = const_value->Image(); //case value condition
			}
			
			VeriStatement *stmt = item->GetStmt(); //u get the case body for the above case condition
			VeriBlockingAssign *assign_stmt = static_cast<VeriBlockingAssign*>(stmt);
			VeriExpression *lhs_expr = assign_stmt->GetLVal();
		//VeriIdRef *id_ref = (VeriIdRef *)lval;
			VeriExpression *rhs_expr = assign_stmt->GetValue();
		
			if(rhs_expr->GetClassId() == ID_VERIIDREF){
				Assign_var *var_node= new Assign_var;
				Initialize_values(NULL, NULL,NULL,var_node,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
				VeriIdRef *id_ref = (VeriIdRef *)lhs_expr;
				val_name = id_ref->GetName(); //left expr
				id_ref = (VeriIdRef *)rhs_expr;
	     			net_name = id_ref->GetName(); // right expr
				
				case_exprn->expression_vt = var_node;
				case_exprn->expression_ct = NULL;
				
				
				//InsertCaseInBlock(al_node, case_expr);
				}
			 else if(rhs_expr->GetClassId() == ID_VERICONSTVAL){
			 	Assign_const *const_node = new Assign_const;
			 	Initialize_values(NULL, NULL,NULL,NULL,const_node,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
				VeriIdRef *id_ref = (VeriIdRef *)lhs_expr;
				val_name = id_ref->GetName(); //left expr
				VeriConstVal *constant_value = static_cast<VeriConstVal*>(rhs_expr);
	 			const_node->const_expr = constant_value->Image(); //right expr
	     			const_node->const_value = constant_value->Integer();//right expr

	     			case_exprn->expression_ct = const_node;
	     			case_exprn->expression_vt = NULL;
	     			}
	     			
	     			
	     		DeclareData *d_node = NULL;
	     		for(d_node = first_data_node ; d_node!= NULL;d_node = d_node->next_n){  //CHANGED HERE
	      			if(d_node->name == val_name){ //left expr
	        			if(case_exprn->expression_vt && !case_exprn->expression_ct){
	        				case_exprn->expression_vt->left_value = new DeclareData;
		  				assign_value(case_exprn->expression_vt->left_value , d_node);
		  				//break;
		  				}
					else if(case_exprn->expression_ct && !case_exprn->expression_vt){
						case_exprn->expression_ct->left_value = new DeclareData;
		  			 	assign_value(case_exprn->expression_ct->left_value ,d_node);
		  			 	//break;
		  			 	}
				checkl = true;
	      
	     			}
	     			else if(net_name && d_node->name == net_name){ //right expr
	       				if(case_exprn->expression_vt && !case_exprn->expression_ct){
	       				case_exprn->expression_vt->right_value = new DeclareData;
		 			assign_value(case_exprn->expression_vt->right_value, d_node);
		 			//CHANGED HERE
		 			tmpnode = new DeclareData;
		 			assign_value(tmpnode,d_node);
		 			insert_in_list(al_node->event_controls,tmpnode);
		 			}
	       // else if(assign_const_node && !assign_var_node)
	       //assign_value(assign_const_node->right_value, d_node);
	       			checkr = true;
	     			}
	     		if(checkl && checkr)
	       		break;
	     		else
	       		continue;
	  		}
	  	checkl = false;checkr = false;
		InsertCaseInBlock(al_node,case_exprn);
		}
		break;
	} //end of case statement option
	case ID_VERISEQBLOCK:
	{
		VeriSeqBlock *seq_block = static_cast<VeriSeqBlock*>(statement);
		Array *statements = seq_block->GetStatements();
		VeriStatement *stmt;
		unsigned j;
		delete_ports_list(al_node->event_controls);
		//EDITED HERE
		delete al_node;
		al_node=NULL;
		seqflag = true;
		//always node is built without event controls list
		FOREACH_ARRAY_ITEM(statements, j, stmt){
			al_node = new Always_block;
			Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,al_node,NULL,NULL,NULL,NULL);
			CreateNodesInAlwaysBlock(stmt , al_node,false,seqflag);
			Insert_event_controls(al_node); //put appropriate event controls for every always node formed
			Insert_in_always_list(al_node);
		
		}
		break;
	}
	
	case ID_VERIBLOCKINGASSIGN:
	{
		//if(statement->GetClassId() == ID_VERISEQBLOCK){
			
		//ComplexOp_node *comp_op = NULL;
		const char *in_left_name = NULL,*in_right_name = NULL;
		bool equalcond=false,constflag = false;
		Operate_node *operation_expr = NULL; //solely for state operation nodes OR operation nodes using '|' operators
		DeclareData *tmpnode=NULL,*outnode=NULL;
		Ifthenelse_block *tmpn=NULL , *condblock_orig = NULL;
		unsigned oper_type , temptype;
		unsigned i;
		
		Ifthenelse_block *condblock = new Ifthenelse_block;
		Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,condblock,NULL,NULL,NULL,NULL,NULL);
		if(!al_node->event_controls){
			al_node->event_controls = new PortList;
			Initialize_values(NULL, al_node->event_controls,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
		}
		
		VeriBlockingAssign *assign_stmt = static_cast<VeriBlockingAssign*>(statement) ;
		VeriExpression *lhs_expr = assign_stmt->GetLVal() ; // Get LHS (this is the output value)
		VeriIdRef *idref = (VeriIdRef*)lhs_expr;
		const char *out_name = idref->GetName();//output variable of the expression
		condblock_orig = condblock;
		
		VeriExpression *rhs_expr = assign_stmt->GetValue() ; // Get Value
		
		if(rhs_expr->GetClassId()==ID_VERIBINARYOPERATOR){
			VeriBinaryOperator *bin_op = static_cast<VeriBinaryOperator*>(rhs_expr) ;
			VeriExpression *left = bin_op->GetLeft(); //left expr of the binary operator
			temptype = bin_op->OperType();
			
			if(left->GetClassId()==ID_VERIMULTICONCAT){
				VeriMultiConcat *multi_concat = static_cast<VeriMultiConcat*>(left);
				// u have to use Array of expressions!!
				Array *expr_arr = multi_concat->GetExpressions();
				VeriExpression *exprn ;
				FOREACH_ARRAY_ITEM(expr_arr, i,exprn){
					VeriIdRef *var = (VeriIdRef*)exprn;
					in_left_name = var->GetName();
				}
				
			}
			else if(left->GetClassId() == ID_VERIIDREF){
				VeriIdRef *varname = (VeriIdRef*)left;
				in_left_name = varname->GetName();
				if(temptype == VERI_REDOR){
					delete condblock;condblock=NULL;
					operation_expr = new Operate_node;
					Initialize_values(NULL, NULL,operation_expr,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
					operation_expr->input_list = new PortList;
					Initialize_values(NULL,operation_expr->input_list,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
				}
			}
			else if(left->GetClassId() == ID_VERIINDEXEDID){ //this is for 
				
				VeriIndexedId *indexed_id=  static_cast<VeriIndexedId*>(left);
				in_left_name = indexed_id->GetName();			
			}
			
			else{
			
			//if left expression then, the condblock doesnt require equal condition,
			//this case arises if the left is VERIBINARYOPERATOR
					
		
				CreateComplexOperations(left,condblock, true , 0,true,iter,operation_expr);
				if(condblock && condblock->else_expr_block)
					condblock = condblock->else_expr_block;
				
			}
			
			VeriExpression *right = bin_op->GetRight(); //second input variable of the expression
			
			if(right->GetClassId() == ID_VERIUNARYOPERATOR){
			//in most cases, it will be a REDNOR operation
			
				VeriUnaryOperator *un_op = static_cast<VeriUnaryOperator*>(right);
				//put operator type: unsigned oper_type = un_op->Opertype(); where to attach this operator to????
				VeriExpression *arg = un_op->GetArg();
				 oper_type = un_op->OperType();
			//only if its a rednor op, then the expression is an equal condition
				if(oper_type == VERI_REDNOR){
					condblock->equal_condition = new Assign_const;
					Initialize_values(NULL,NULL,NULL,NULL,condblock->equal_condition,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
					VeriBinaryOperator *bin_op = static_cast<VeriBinaryOperator*>(arg) ;
					if(bin_op){
						VeriExpression *left_expr = static_cast<VeriExpression*>(bin_op);
						VeriIdRef *bin_left = (VeriIdRef*)left_expr;
							//equal condition completed here
						condblock->equal_condition->left_value = new DeclareData;
						Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,condblock->equal_condition->left_value,NULL,NULL,NULL);
						condblock->equal_condition->left_value->name=bin_left->GetName();
						VeriExpression *right_expr = static_cast<VeriExpression*>(bin_op);
						VeriConstVal *constval = static_cast<VeriConstVal*>(right_expr);
						
						condblock->equal_condition->const_expr = constval->Image();
						//in_right_name = bin_left->GetName();
						equalcond=true; //this is for indicating there is equalcondition
					}
				}
				else if(arg->GetClassId()==ID_VERIIDREF){
					//this case shows something like outimg = ST1_03d & (~RG_22);
					VeriIdRef *ref = (VeriIdRef *)arg;
					//if the expression is a variable
					if(ref) in_right_name = ref->GetName();
					if(condblock)
						equalcond=true;
				}
				//else if the expression is an operation
				else if(arg->GetClassId()==ID_VERIBINARYOPERATOR){
					VeriBinaryOperator *bin_op = static_cast<VeriBinaryOperator*>(arg);
					
					//control signals
					VeriExpression *left = static_cast<VeriExpression*>(bin_op);
					//while loop for extracting all the variables in the left expr in case its a nested binary operation
					//insert the variables in the list  of if_condition_var
					CreateComplexOperations(left,condblock,true,0,true,iter,operation_expr);
					if(condblock && condblock->else_expr_block)
						condblock = condblock->else_expr_block;
				}
				
			
			}
			else if(right->GetClassId() == ID_VERIIDREF){
			//if VERIIDREF
				VeriIdRef *var = (VeriIdRef*)right;
				in_right_name = var->GetName();
				if(temptype == VERI_REDOR && condblock){
					delete condblock;condblock = NULL;
					operation_expr = new Operate_node;
					Initialize_values(NULL, NULL,operation_expr,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
					operation_expr->input_list = new PortList;
					Initialize_values(NULL,operation_expr->input_list,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
				}
			}
			else if(right->GetClassId() == ID_VERIINDEXEDID){ //this is for a variable with indexes..index is ignored
				
				VeriIndexedId *indexed_id=  static_cast<VeriIndexedId*>(right);
				in_right_name = indexed_id->GetName();	
				if(temptype == VERI_REDOR && condblock){
					delete condblock;condblock = NULL;
					operation_expr = new Operate_node;
					Initialize_values(NULL, NULL,operation_expr,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
					operation_expr->input_list = new PortList;
					Initialize_values(NULL,operation_expr->input_list,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
				}		
			}
			else if(right->GetClassId() == ID_VERICONSTVAL){
			
				 VeriConstVal *constant_value = static_cast<VeriConstVal*>(right);
	    			 in_right_name = constant_value->Image(); //right expr
	    			 constflag = true;
			}
			//create the else part of the conditional block 
			
			else if(right->GetClassId()==ID_VERIBINARYOPERATOR){
				if(condblock){
					condblock->else_expr_block = new Ifthenelse_block;
					Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,condblock->else_expr_block,NULL,NULL,NULL,NULL,NULL);
					CreateComplexOperations(right , condblock->else_expr_block, true , 0,true,iter,operation_expr);
				}
				else //for operation_expr
					CreateComplexOperations(right , condblock, true , 0,true,iter,operation_expr);
				//Insert the complex op in the list of complex ops in always node
				
			}
		}
			if(condblock)
				condblock = condblock_orig;
			
			//create the then expr part only if there is no equalcondition
			if(condblock && !condblock->then_expr_var && !equalcond){
				condblock->then_expr_var = new Assign_var;
				Initialize_values(NULL,NULL,NULL,condblock->then_expr_var,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
			}
			
					
			DeclareData *t_node=NULL;
			// insert the variables from datalist to the appropriate expression of the condblock
			for(t_node=first_data_node ; t_node!= NULL; t_node = t_node->next_n){
					if(t_node->name == out_name){
						if(operation_expr){ //if its an operation involving states only
						//this indicates that condblock is deleted
							operation_expr->output= new DeclareData;
							assign_value(operation_expr->output,t_node);
						}
						
						else if(condblock && !equalcond){
							condblock->then_expr_var->left_value = new DeclareData;
							assign_value(condblock->then_expr_var->left_value, t_node);
							//if the condblock has an else expression, then the output of the else expr also gets the same out_name
							if(condblock && condblock->else_expr_block){
								tmpn = condblock->else_expr_block;
								while(tmpn){
									tmpn->then_expr_var->left_value = new DeclareData;
									assign_value(tmpn->then_expr_var->left_value, t_node);
									tmpn = tmpn->else_expr_block;
								}
							}
							outnode= new DeclareData;
							assign_value(outnode,t_node);
						}
						else if(condblock && equalcond){
							condblock->then_var = new DeclareData;
							assign_value(condblock->then_var , t_node);
						}
						
					}
					//in_left_name being a state does not prove its a solely state operation
					else if(t_node->name == in_left_name){
						 if(Search_var_InStateList(t_node , first_state)){
						 	
							tmpnode = new DeclareData;
							assign_value(tmpnode , t_node);
							if(operation_expr) insert_in_list(operation_expr->input_list,tmpnode);
							else if(condblock){
								condblock->if_condition_var  = new DeclareData;
								assign_value(condblock->if_condition_var, t_node); 
							}	
						 }
						 //if a non state variable is the condition var, then only conditional node shall get it
						 else if(condblock){
						 	condblock->if_condition_var  = new DeclareData;
							assign_value(condblock->if_condition_var, t_node); 
						 }
						 else if(operation_expr){
						 	tmpnode = new DeclareData;
						 	assign_value(tmpnode,t_node);
						 	insert_in_list(operation_expr->input_list,tmpnode);
						 }
						 
					}
					else if(t_node->name == in_right_name){
						if(Search_var_InStateList(t_node,first_state)){
							if(condblock && !operation_expr){
								Delete_cond_node(condblock);
								delete condblock;
								condblock=NULL;
								operation_expr = new Operate_node;
								Initialize_values(NULL, NULL,operation_expr,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
								operation_expr->input_list = new PortList;
								Initialize_values(NULL,operation_expr->input_list,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
							}
							DeclareData *node = new DeclareData;
							assign_value(node , t_node);
							insert_in_list(operation_expr->input_list,node);
							if(tmpnode) insert_in_list(operation_expr->input_list,tmpnode);//insert the in_left_name also
							if(outnode) operation_expr->output = outnode; //put the output if it has been created before this case
						}
						//EDITED HERE
						else if(condblock && equalcond){ // this is for the condition when the in_right_name is similar to ~RG_22
							if(!condblock->equal_condition){
								condblock->equal_condition = new Assign_const;
								Initialize_values(NULL,NULL,NULL,NULL,condblock->equal_condition,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
							}
							condblock->equal_condition->left_value = new DeclareData;
							assign_value(condblock->equal_condition->left_value,t_node);
							condblock->equal_condition->left_value->unary_operator = oper_type;
							condblock->equal_condition->const_expr = new char;
							condblock->equal_condition->const_expr = "0";
						}
						//this case will not arise if it is equal condition
						else if(condblock && !equalcond){
							condblock->then_expr_var->right_value = new DeclareData;
							assign_value(condblock->then_expr_var->right_value,t_node);
						}
						else if(operation_expr){
							DeclareData *node = new DeclareData;
							assign_value(node , t_node);
							insert_in_list(operation_expr->input_list,node);
						}
					}
				
			}
			//the case if the rhsvalue of the assignment is a constant value, in_right_name wont be assigned above
			if(constflag){
				condblock->then_expr_var->right_value = new DeclareData;
				Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,condblock->then_expr_var->right_value,NULL,NULL,NULL);
				condblock->then_expr_var->right_value->name=in_right_name;
			}
			
			if(condblock){
				al_node->CondBlock = condblock;
				delete outnode; outnode=NULL;
				if(tmpnode){ delete tmpnode;tmpnode=NULL;}
			}
			else if(operation_expr)
				al_node->operate_expr = operation_expr;
			//else if( compexpr)
			//	al_node->comp_expr = compexpr;
			
			

	break;
		
	}
	
	
	}// end of switch statement
	
	}	// end of the function
		
			
		// all case items are part of the case statement block
		// each item is attached to the list of the case items, each node is a casestatement_struct and this list shall be attached to the always block
		
		
		
	void InsertCaseInBlock( Always_block *al_node , Case_Statement *expr){
	
	
	Case_Statement *temp = NULL;
	
	//if(al_node->CaseBlock->next_n == NULL)
	//	al_node->CaseBlock->next_n = expr;
	//else{
		for(temp = al_node->CaseBlock; temp->next_n != NULL; temp = temp->next_n);
		temp->next_n = expr;
		expr->prev_n = temp;
		expr->next_n = NULL;
		
	//	}
	}
		
		

//FUNCTION TO INSERT THE EVENT CONTROL VARIABLES FOR ALWAYS NODE

	
void Insert_event_controls(Always_block *node){

DeclareData *tmp=NULL;
DeclareData *tmpnode=NULL;
Ifthenelse_block *cond=NULL;

cond = node->CondBlock;

if(node->CondBlock){
	while(cond){
		if(cond->equal_condition){
			tmp = new DeclareData;
			assign_value(tmp, cond->equal_condition->left_value);
			insert_in_list(node->event_controls , tmp);
		}
		else{
			tmp = new DeclareData;
			assign_value(tmp,cond->then_expr_var->right_value);
			insert_in_list(node->event_controls,tmp);
		}
		tmp = new DeclareData;
		assign_value(tmp,cond->if_condition_var);
		insert_in_list(node->event_controls,tmp);
		cond = cond->else_expr_block;
	}

}
if(node->operate_expr){
	tmp = node->operate_expr->input_list->first_port;
	while(tmp){
		tmpnode = new DeclareData;
		assign_value(tmpnode,tmp);
		insert_in_list(node->event_controls,tmpnode);
		tmp = tmp->next_n;
	}
}


}



void Delete_list(PortList *control_list , DeclareData *var){

DeclareData *node = NULL, *node_next = NULL;

for(node = control_list->first_port ; node ; node = node_next){
	node_next = node->next_n;
	
	if(var->name == node->name)
	continue;
	else{
	if(node->name){ 
	delete node->name;
	node->name = NULL;
	}
	delete node;
	node=NULL;
	}
}
control_list->first_port = NULL;
//if(control_list->port_name) delete control_list->port_name;

//delete control_list;
//control_list = NULL;
}
	
//function to delete an unwanted conditional node
void Delete_cond_node(Ifthenelse_block *condnode){

Ifthenelse_block *tmp = NULL;
tmp = condnode;
while(tmp){
	delete tmp->if_condition_var;
	tmp->if_condition_var= NULL;
	if(tmp->equal_condition){
		 delete tmp->equal_condition->left_value;
		 tmp->equal_condition->left_value=NULL;
		 delete tmp->equal_condition;
		 tmp->equal_condition=NULL;
	}
	delete tmp->then_expr_var->left_value;
	delete tmp->then_expr_var->right_value;
	delete tmp->then_expr_var;
	tmp->then_expr_var=NULL;
	
	tmp = tmp->else_expr_block;
}

}



// create function for case statement node: convert case statement into ifthenelse node under the always node



//function for inserting conditional blocks in the list under always node

 void InsertOpInAlwaysblock(Always_block *al_node , Operate_node *basicop_expr , Ifthenelse_block *condexpr){
 
 Operate_node *tmp1 = NULL;
 Ifthenelse_block *tmp2 = NULL;
 
 //for basic op
 if(basicop_expr){
 	for(tmp1 = al_node->operate_expr ; tmp1->next_op!=NULL; tmp1 = tmp1->next_op);
 	tmp1->next_op = basicop_expr;
 	basicop_expr->prev_op = tmp1;
 	basicop_expr->next_op = NULL;
 }
 //for conditional block
 /*else{
 	for(tmp2 = al_node->CondBlock ; tmp2->next_block!=NULL; tmp2 = tmp2->next_block);
 	tmp2->next_block = condexpr;
 	condexpr->prev_block = tmp2;
 	condexpr->next_block = NULL;
 	}
 */	
 }



//operate flag is to indicate whether the expression is left or right
//basicop will indicate if its the first time entering BINARYOPERATOR,indicating its a first ifthen expr
//basicop flag is to indicate if the first ifthen expr is being created or the elseexpr is being created
//if there are more than two state variables,then compexpr is created
void CreateComplexOperations( VeriExpression *expression , Ifthenelse_block*& condexpr, bool basicop , unsigned unary_type,bool operate,int &iteration, Operate_node*& oper_expr){
// if basicop is true, put in basicop1 or else basicop2

DeclareData *tnode=NULL;
DeclareData *in_node=NULL;
unsigned optype;

	if(!expression) return;
	
	switch(expression->GetClassId()){
	//EDITING IN PROGRESS
	case ID_VERIBINARYOPERATOR:
	{
	VeriBinaryOperator *bin_op = static_cast<VeriBinaryOperator*>(expression) ;
	
	
	//comp_exp->basic_operand = NULL;
	VeriExpression *leftexp = bin_op->GetLeft();
	//operate flag will be true in this case
	
	optype = leftexp->OperType();
	if((leftexp->GetClassId()!= ID_VERIBINARYOPERATOR && bin_op->OperType() == VERI_REDOR) || (leftexp->GetClassId() == ID_VERIBINARYOPERATOR && optype == VERI_REDOR)){
		if(condexpr){
			delete condexpr;condexpr = NULL;
		}
		if(!oper_expr){
			oper_expr = new Operate_node;
			Initialize_values(NULL, NULL,oper_expr,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
			oper_expr->input_list = new PortList;
			Initialize_values(NULL,oper_expr->input_list,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
		}
		
	}
	if(basicop){

		//basicop=false;
		CreateComplexOperations(leftexp,condexpr, true,unary_type,true,iteration,oper_expr);
		basicop=false;
		iteration=0;
	
	}	
	else if(!basicop && operate){
		if(condexpr){
			condexpr->else_expr_block = new Ifthenelse_block;
			Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,condexpr->else_expr_block,NULL,NULL,NULL,NULL,NULL);
		}
		CreateComplexOperations(leftexp,condexpr->else_expr_block, true,unary_type,true,iteration,oper_expr);
	}
	
	
	// get the right expression of this bin_op
	VeriExpression *rightexp = bin_op->GetRight();
	// now operate flag will be false
	optype = rightexp->OperType();
	
	if((rightexp->GetClassId()!= ID_VERIBINARYOPERATOR && bin_op->OperType() == VERI_REDOR) || (rightexp->GetClassId() == ID_VERIBINARYOPERATOR && optype == VERI_REDOR)){
		//delete the condexpr once its found that one of the sub-expressions have OR operation.
		if(condexpr){
			delete condexpr;condexpr = NULL;
		}
		if(!oper_expr){
			oper_expr = new Operate_node;
			Initialize_values(NULL, NULL,oper_expr,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
			oper_expr->input_list = new PortList;
			Initialize_values(NULL,oper_expr->input_list,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
		}
		
	}
	
	if(rightexp->GetClassId() == ID_VERIBINARYOPERATOR && !iteration){
		if(condexpr){
			 condexpr->else_expr_block= new Ifthenelse_block;
			 Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,condexpr->else_expr_block,NULL,NULL,NULL,NULL,NULL);
			 CreateComplexOperations(rightexp,condexpr->else_expr_block, true,unary_type,true,iteration,oper_expr);
                      
			
		}
		else
			CreateComplexOperations(rightexp,condexpr, true,unary_type,true,iteration,oper_expr);
		
		
	}
	else{
		if(condexpr){
			condexpr->then_expr_var = new Assign_var;
			 Initialize_values(NULL, NULL,NULL,condexpr->then_expr_var,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
		 }
		CreateComplexOperations(rightexp,condexpr, true,unary_type,false,iteration,oper_expr);
	}
	
	break;
	}
	
	case ID_VERIINDEXEDID:
	
	case ID_VERIIDREF:
	{
	const char *varname = NULL;
	DeclareData *node = NULL;
	
	//then check basicop is true or false
	//there is no output for any basicop nodes, so either its op1 or op2 input list, which can be checked using the flag
	VeriIdRef *idref = (VeriIdRef*)expression;
	varname = idref->GetName();
	
	//insert in op1 input list
	for(node = first_data_node ; node!= NULL; node=node->next_n){
		if(node->name == varname){
			//if its a left expression and the function has the first ifthen block expr and not else expr
			// if the iteration value is between 1 and 2, there are two state signals part of oper_expr, if iteration>=3 then its a complex operation
			if(Search_var_InStateList(node,first_state)){
				if((iteration>=1 && iteration<2) || iteration>=2){
					if(condexpr){
						Delete_cond_node(condexpr);
						delete condexpr;
						condexpr=NULL;
					}
					if(!oper_expr){
						oper_expr = new Operate_node;
						Initialize_values(NULL, NULL,oper_expr,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
						oper_expr->input_list = new PortList;
						Initialize_values(NULL, oper_expr->input_list,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
					}
					iteration++;
					tnode = new DeclareData;
					assign_value(tnode,node);
					insert_in_list(oper_expr->input_list,tnode);
					
				}
				//only if the oper_expr exists, doesnt matter what the value of iteration is. the oper_expr->input_list should have the state value
				else if(oper_expr){
					iteration++;
					tnode = new DeclareData;
					assign_value(tnode,node);
					insert_in_list(oper_expr->input_list,tnode);
				}
				else	iteration++;
				
			}
			if(oper_expr && !Search_var_InStateList(node,first_state)){ //this case for input signals(continuousassign) which are not state signal
				tnode = new DeclareData;
				assign_value(tnode,node);
				if(oper_expr->input_list) insert_in_list(oper_expr->input_list,tnode);
			}
			else if(condexpr && operate==true && basicop && iteration<=1){
				in_node = new DeclareData;
				assign_value(in_node , node);
				if(!condexpr->if_condition_var){
					 condexpr->if_condition_var = in_node;
					condexpr->if_condition_var->unary_operator = unary_type;
				}	 
				// if there are more than one condition variable in the rhs expr
				else Insert_var_list(condexpr->if_condition_var, in_node);
				operate=false;
			}
			else if(condexpr && !operate && basicop && iteration<=1){
				condexpr->then_expr_var->right_value = new DeclareData;
				assign_value(condexpr->then_expr_var->right_value,node);
				condexpr->then_expr_var->right_value->unary_operator = unary_type;
			}
			else if(condexpr && !basicop && operate && iteration<=1){
				condexpr = condexpr->else_expr_block;
				assign_value(condexpr->if_condition_var , node);
				condexpr->if_condition_var->unary_operator = unary_type;
				operate=false;
			}
			else if(condexpr && !basicop && !operate && iteration<=1){
				condexpr = condexpr->else_expr_block;
				condexpr->then_expr_var->right_value = new DeclareData;
				assign_value(condexpr->then_expr_var->right_value,node);
			}
		
			break;
		}
		
	}
	break;
	
	}
	case ID_VERICONCAT:
	{
	VeriConcat *concat = static_cast<VeriConcat*>(expression);
	Array *expr_arr = concat->GetExpressions();
	unsigned i;
	VeriExpression *expr;
	FOREACH_ARRAY_ITEM(expr_arr, i, expr) {
		if(expr->GetClassId()==ID_VERICONSTVAL)
			continue;
		else if(basicop && operate)
			CreateComplexOperations(expr,condexpr, true, unary_type,true,iteration,oper_expr);
		else if(operate && !basicop)
			CreateComplexOperations(expr,condexpr, false,unary_type,true,iteration,oper_expr);
		else if(!operate && !basicop)
			CreateComplexOperations(expr,condexpr, false,unary_type,false,iteration,oper_expr);
		else if(!operate && basicop)
			CreateComplexOperations(expr,condexpr, true,unary_type,false,iteration,oper_expr);
	}
	break;	
	
	}
	case ID_VERIMULTICONCAT:
	{
	VeriMultiConcat *multi_concat = static_cast<VeriMultiConcat*>(expression);
	Array *expr_arr = multi_concat->GetExpressions();
	unsigned i;
	VeriExpression *expr;
	FOREACH_ARRAY_ITEM(expr_arr, i,expr){
			if(expr->GetClassId()==ID_VERICONSTVAL)
				continue;
			else if(basicop && operate)
				CreateComplexOperations(expr,condexpr, true,unary_type,true,iteration,oper_expr);
			else if(basicop && !operate)
				CreateComplexOperations(expr,condexpr, true,unary_type,false,iteration,oper_expr);
			else if(operate && !basicop)
				CreateComplexOperations(expr,condexpr, false,unary_type,true,iteration,oper_expr);
			else if(!operate && !basicop)
				CreateComplexOperations(expr,condexpr, false,unary_type,false,iteration,oper_expr);
	}
	break;
	}
	
	case ID_VERIUNARYOPERATOR:
	{
	VeriUnaryOperator * un_op = static_cast<VeriUnaryOperator*>(expression) ;
	VeriExpression *arg_expr = un_op->GetArg();
	unary_type = un_op->OperType();
	if(basicop && operate)
		CreateComplexOperations(arg_expr,condexpr, true, unary_type,true,iteration,oper_expr);
	else if(operate && !basicop)
		CreateComplexOperations(arg_expr,condexpr, false,unary_type,true,iteration,oper_expr);
	else if(!operate && !basicop)
		CreateComplexOperations(arg_expr,condexpr, false,unary_type,false,iteration,oper_expr);
	else if(!operate && basicop)
		CreateComplexOperations(arg_expr,condexpr, true,unary_type,false,iteration,oper_expr);
	break;
	}
	
	case ID_VERICONSTVAL:
	{
	const char *varname=NULL;
	VeriConstVal *constant_value = static_cast<VeriConstVal*>(expression);
	varname = constant_value->Image();
	if(basicop && condexpr){
		if(condexpr->else_expr_block)
			condexpr = condexpr->else_expr_block;
		condexpr->then_expr_var->right_value = new DeclareData;
		Initialize_values(NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL,condexpr->then_expr_var->right_value,NULL , NULL,NULL);
		condexpr->then_expr_var->right_value->name = varname;
		condexpr->then_expr_var->right_value->data_type=integer;
	
	}
		
	break;
	}
	
   } //end of switch
} //end of function	
		

//fn to delete the variable list of the graph_first_node
void delete_var_list(Graph_node *graphnode,DeclareData*& varlist){

DeclareData *tmp = NULL;
DeclareData *tmp_next = NULL;

if(graphnode){
	tmp = graphnode->data_node;
	
	while(tmp){
		tmp_next = tmp->next_n;
		delete tmp;
		tmp = NULL;
		
		tmp = tmp_next;
	}
	graph_first_node->data_node = NULL;
}
else if(varlist){
	while(varlist){
		tmp_next = varlist->next_n;
		delete varlist ;
		varlist = NULL;
		varlist = tmp_next;
	}
}
}



