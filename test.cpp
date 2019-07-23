
//operate flag is to indicate whether the expression is left or right
//basicop will indicate if its the first time entering BINARYOPERATOR,indicating its a first ifthen expr
//basicop flag is to indicate if the first ifthen expr is being created or the elseexpr is being created
void CreateComplexOperations( VeriExpression *expression , Ifthenelse_block *condexpr, bool basicop , unsigned unary_type,bool operate,int iteration, Operate_node *oper_expr){
// if basicop is true, put in basicop1 or else basicop2

DeclareData *tnode=NULL;

	if(!expression) return;
	
	switch(expression->GetClassId()){
	//EDITING IN PROGRESS
	case ID_VERIBINARYOPERATOR:
	{
	VeriBinaryOperator *bin_op = static_cast<VeriBinaryOperator*>(expression) ;
	
	//comp_exp->basic_operand = NULL;
	VeriExpression *leftexp = bin_op->GetLeft();
	//operate flag will be true in this case
	if(basicop){

		//basicop=false;
		CreateComplexOperations(leftexp,condexpr, true,unary_type,true,iteration,oper_expr);
		basicop=false;
		iteration=0;
	
	}	
	else if(!basicop && operate){
		condexpr->else_expr_block = new Ifthenelse_block;
		CreateComplexOperations(leftexp,condexpr->else_expr_block, true,unary_type,true,iteration,oper_expr);
	}
	
	
	// get the right expression of this bin_op
	VeriExpression *rightexp = bin_op->GetRight();
	// now operate flag will be false
	
	if(rightexp->GetClassId() == ID_VERIBINARYOPERATOR && !iteration){
		condexpr->else_expr_block= new Ifthenelse_block;
		CreateComplexOperations(rightexp,condexpr->else_expr_block, true,unary_type,true,iteration,oper_expr);
	}
	else{
		condexpr->then_expr_var = new Assign_var;
		CreateComplexOperations(rightexp,condexpr, true,unary_type,false,iteration,oper_expr);
	}
	
	break;
	}
	
	
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
			if(Search_var_InStateList(node,first_state)){
				if(iteration>=1){
					delete condexpr;
					condexpr=NULL;
					oper_expr = new Operate_node;
					Initialize_values(NULL, NULL,oper_expr,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
					oper_expr->input_list = new PortList;
					Initialize_values(NULL, oper_expr->input_list,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
					iteration++;
					tnode = new DeclareData;
					assign_value(tnode,node);
					insert_in_list(oper_expr->input_list,tnode);
				}
				else	iteration++;
				
			}
			if(operate==true && basicop && iteration<=1){
				condexpr->if_condition_var = new DeclareData;
				assign_value(condexpr->if_condition_var , node);
				condexpr->if_condition_var->unary_operator = unary_type;
				operate=false;
			}
			else if(!operate && basicop && iteration<=1){
				condexpr->then_expr_var->right_value = new DeclareData;
				assign_value(condexpr->then_expr_var->right_value,node);
				condexpr->then_expr_var->right_value->unary_operator = unary_type;
			}
			else if(!basicop && operate && iteration<=1){
				condexpr = condexpr->else_expr_block;
				assign_value(condexpr->if_condition_var , node);
				condexpr->if_condition_var->unary_operator = unary_type;
				operate=false;
			}
			else if(!basicop && !operate && iteration<=1){
				condexpr = condexpr->else_expr_block;
				condexpr->then_expr_var->right_value = new DeclareData;
				assign_value(condexpr->then_expr_var->right_value,node);
			}
		
			break;
		}
		//EDITING IN PROGRESS
		/*if(Search_var_InStateList(node,first_state)){
			if(iteration>1){
				delete condexpr;
				condexpr=NULL;
				oper_expr = new Operate_node;
				Initialize_values(NULL, NULL,oper_expr,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
				oper_expr->input_list = new PortList;
				Initialize_values(NULL, oper_expr->input_list,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
				iteration++;
				tnode = new DeclareData;
				assign_value(tnode,node);
				insert_in_list(oper_expr->input_list,tnode);
			}
			else	iteration++;
			break;
		}*/
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
		if(basicop && operate)
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
