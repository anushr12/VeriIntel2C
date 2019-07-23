	if(tmp->place_ptr){
				tmp_place = tmp->place_ptr;
				while(tmp_place && Search_var_in_InputList(tmp,tmp_place)){
					tmpvar = tmp_place->first_place_input;
					while(tmpvar){
						endnode = NULL;controlnode = NULL;block_ret = NULL;
						//check if tmpvar is available in basicblock,if yes,also check how much of the path has been already created from endnode and then use endnode_actual to insert the rest of the path
						if((Search_end_node_BasicBlock(tmpvar,first_basic_block,endnode,controlnode,true,block_ret,false,NULL) && Check_creation_of_path(endnode,tmpvar,endnode_actual)) || Check_parent_nodes(tmpvar,first_state,NULL,controlnode,endnode,block_ret)){
							//Insert_path_in_BasicBlock(controlnode,block_ret,tmpvar,first_state,endnode_actual,false);
							Create_subnodes_under_endnode(endnode,NULL,controlnode,block_ret,tmp_place,block_null,equalnode,NULL,tmpop,NULL,'p');
							place_done=true;
							
						}
						else if(Search_control_nodes(NULL,controlnode,endnode,tmpvar,NULL)){
							if(!controlnode->bb_ptr){
								controlnode->bb_ptr = new Basic_block;
								Initialize_nodes(NULL,NULL,NULL,NULL,controlnode->bb_ptr,NULL);
							}
							Create_subnodes_under_endnode(endnode,NULL,controlnode,controlnode->bb_ptr,tmp_place,block_null,equalnode,NULL,tmpop,NULL,'p');
						}
						else place_done=false;	
						
						tmpvar = tmpvar->next_n;
					}
					tmp_place = tmp_place->next_place;
				}
				if(place_done){
					path_done=true;
					break;
				}
			}
			
/*********************************** ORIGINAL PIECE END ***********************************************/	
			
if(tmp->place_ptr){

	tmp_place = tmp->place_ptr;
	while(tmp_place && Search_var_in_InputList(tmp,tmp_place)){
		var = tmp_place->first_trans_node->data_node->condition_op->assign_expr->rhs_value;
		var_next = tmp_place->first_trans_node->output_var;
		if(Search_end_node_BasicBlock(var,first_basic_block,endnode,controlnode,true,block_ret,false,NULL)){
			if(Check_creation_of_path(endnode,var_next,endnode_actual)){
				basicblock_loop = block_ret;
				place_done = true;
				break;
			}
			else{
				if(Search_control_nodes(NULL,control_attach,node_attach,tmp,NULL) && control_attach == controlnode)
					Create_subnodes_under_endnode(endnode,NULL,controlnode,block_ret,tmp_place,block_null,equalnode,NULL,tmpop,NULL,'p');
			
				else if(Search_control_nodes(NULL,control_attach,node_attach,tmp,NULL)){
					if(!control_attach->bb_ptr) control_attach->bb_ptr = block_ret;
					else Insert_in_BasicBlock_list(control_attach,block_ret);
					//this var node should be showing the equal node which 
					if(!control_attach->control_out) control_attach->control_out = endnode;
				}
				place_done = true;
				break;
			}
		}
		else place_done = false
		tmp_place = tmp_place->next_place;
	}
	if(place_done) break;
	
}
		
return place_done;


if( control_out->compnode || control_out->signalnode || control_out->opnode){
	check = true;
	if(control_out->compnode){
		if(tmpout == control_out->compnode)
			flag = false;
		else tmpout = control_out->compnode->value_out;
		
	}
	if(control_out->signalnode){
		if(!flag)
			tmpout = control_out->signalnode->out_signal;
		else if(flag && !check){
			if(tmpout == control_out->signalnode->out_signal)
				flag = false;
			else tmpout = control_out->signalnode->out_signal;
		}
			
	}
	if(control_out->opnode){
		if(!flag)
			tmpout = control_out->opnode;
		else if(flag && !check){
			if(tmpout == control_out->opnode->output_value)
				tmpout = NULL;
			else
				tmpout = control_out->opnode->output_value;
		}
	}
	
}	
/*******************************************END *********************************************************/

//this part is for creating the control node having comparator and attaching the condition_var
if(Search_end_node_BasicBlock(depth_node, first_basic_block ,end_node,control_node,true, block_ret,false,NULL)){
		Create_control_node(control_create , end_node,NULL,control_prev,first_state,control_node,NULL,tmp_cond,NULL,false);
		control_create->control_in_from_dfg = end_node;
	}
	else if(Check_loop_body(depth_node,first_state,loop_created,loop_dataflow,tmp_exit,false,end_node)){
		Create_control_node(control_create,end_node,NULL, control_prev,first_state,control_node,NULL,tmp_cond,NULL,false);
		//control_create->control_in_
	}
		
	else if(Search_control_nodes(NULL, control_node,end_node,depth_node,NULL)){
		Create_control_node(control_create,end_node,NULL,control_prev,first_state,control_node,NULL,tmp_cond,NULL,false);
		control_create->control_in = control_prev;
	}
	//now change the depth_node to the rhs_value ofthe data part
	depth_node = tmp_cond->assign_expr->rhs_value;
	
//}

//this is the part for the other cases of the switch-case node, attaching the equal nodes in parallel
 if( Search_end_node_BasicBlock(depth_node, first_basic_block ,end_node,control_node,true, block_ret,false,NULL) || Check_parent_nodes(depth_node,first_state,NULL,control_node,end_node,block_ret)){

	//control_node for the case when Check_parentnodes fn is active will be the control_block where similar depth_node is already inserted
		Create_subnodes_under_endnode(end_node,depth_node, control_node , data_block ,NULL,block_ret,tmpeq,tmp_cond->assign_expr,tmpop,NULL,false, 'b');
		
		if(Search_end_node_BasicBlock(tmp_cond->assign_expr->lhs_value,first_basic_block ,end_node,control_node,true, block_ret,false,NULL))
			tmpeq->lhs_value = end_node;
		else{
			tmpeq->lhs_value = new DeclareData;
			assign_value(tmpeq->lhs_value,tmp_cond->assign_expr->lhs_value);
		}
		
		if(!control_create->control_out){
			control_create->control_out = new DeclareData;
			Initialize_values(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,control_create->control_out,NULL,NULL,NULL);
			control_create->control_out->equal_op_out = tmpeq;
		}
		if(!control_create->bb_ptr) control_create->bb_ptr = block_ret;
		if(!control_node->result_control) control_node->result_control = control_create;
		else Insert_in_child_list(control_node->result_control,control_create);
}

/*********************************** END OF ****************************************************/


/**************************** ORIGINAL CODE ***********************************/
//this is for first case only to attach the ifcondition var(case condition variable)
if(!tmp_cond->prev_cond){
	//search for loop node in petri net.. using depth_node
	if(Search_end_node_BasicBlock(depth_node, first_basic_block ,end_node,control_node,true, block_ret,false,NULL)){
		Create_control_node(control_create , end_node,NULL,control_prev,first_state,control_node,NULL,tmp_cond,NULL,false);
		control_create->control_in_from_dfg = end_node;
	}
	else if(Check_loop_body(depth_node,first_state,loop_created,loop_dataflow,tmp_exit,false,end_node)){
		Create_control_node(control_create,end_node,NULL, control_prev,first_state,control_node,NULL,tmp_cond,NULL,false);
		//control_create->control_in_
	}
		
	else if(Search_control_nodes(NULL, control_node,end_node,depth_node,NULL)){
		Create_control_node(control_create,end_node,NULL,control_prev,first_state,control_node,NULL,tmp_cond,NULL,false);
		control_create->control_in = control_prev;
	}
}
//this is the part for the other cases of the switch-case node, attaching the equal nodes in parallel
else if(tmp_cond->prev_cond && ((data_block && Search_end_node_BasicBlock(depth_node,data_block,end_node,control_node,false,block_ret,false,NULL)) || Search_end_node_BasicBlock(depth_node, first_basic_block ,end_node,control_node,true, block_ret,false,NULL) || Check_parent_nodes(depth_node,first_state,NULL,control_node,end_node,block_ret))){

	//control_node for the case when Check_parentnodes fn is active will be the control_block where similar depth_node is already inserted
		Create_subnodes_under_endnode(end_node,depth_node, control_node , data_block ,NULL,block_ret,tmpeq,tmp_cond->assign_expr,tmpop,NULL,false, 'b');
		
		if(Search_end_node_BasicBlock(tmp_cond->assign_expr->lhs_value,first_basic_block ,end_node,control_node,true, block_ret,false,NULL))
			tmpeq->lhs_value = end_node;
		else{
			tmpeq->lhs_value = new DeclareData;
			assign_value(tmpeq->lhs_value,tmp_cond->assign_expr->lhs_value);
		}
	
}
/******************************END OF ORIGINAL *******************************************/


/***************************** Trace_back_node *******************************************************/

bool Trace_back_node(DeclareData *vartosearch, State_var*& ret_state,State_var *first_state,State_var *state_continue ,State_var** state_list,bool state,bool send_all_states,DeclareData *vartmp , bool flag){

State_var *tmpstate = NULL;
State_var *tmp_st = NULL;
DeclareData *tmpst = NULL;
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

if(state)
	tmpstate = first_state;
else	tmpstate = state_continue;

while(tmpstate){

	if(flag) tmpvar = tmpstate->state_name;
	else if(!flag) tmpvar = vartmp;
	while(tmpvar){
		search = false;
		node_down = false;
		if(!strcmp(tmpvar->name , vartosearch->name)){
			search = true;
			if(send_all_states && Search_state_in_list(tmpstate,NULL,state_list,10))
				Insert_in_StateArray_list(tmpstate,state_list,10);
				
			else if(!ret_state) ret_state = tmpstate;
			break;
		}
		//to check if the path following tmpvar is a loop. The loop shouldnt be created here. it returns the exit_nodes as well
		if(!node_down && Check_loop_body(tmpvar,first_state,loop_created,loop_dataflow,exit_node,false,endnode,loopcontrol,false,header_node)){
			//if( Check_exitpoint_of_loop(header_node,NULL,NULL,exit_node,controlnode_check,false,true)){
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
			while(tmp_place && Search_var_in_InputList(tmpvar,tmp_place)){
				//first check all the place inputs(which are not equalto the rhs value of the assignment_graph) and state inputs if they r equal to tmpstate
				tmp_tran = tmpvar->place_ptr->first_trans_node;
				//this function will check all states of the place input n
					if(Check_state_of_place_input(tmp_place , tmpvar , tmpstate,NULL,first_state,state_list,10,cntrl)){
						tmpvar = tmp_tran->output_var;
						if(!strcmp(tmp_tran->output_var->name , vartosearch->name)){
							//ret_state should not be used when send_all_states is true
							if(send_all_states && state_list)
								ret_state = NULL;
							
							else
								ret_state = tmpstate;
							search = true;
							break;
						}
						else
							// this is for searching vertically tracing one transition output
							continueflag = true;
							//break;
						
					}
					else continueflag=false;
					
				if(search) tmp_place=NULL;
				else if(!continueflag) tmp_place = tmp_place->next_place;
				else break; //THIS is going depthwise inside
			} //endof place
			if(!search && continueflag) continue;		//THIS is going depthwise inside
			else node_down = false;
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
						//search for the tmp_st in ret_state, if yes,leave it otherwise insert this state in state_list
						if(send_all_states && !Search_state_in_list(tmp_st,NULL,state_list,10))
							Insert_in_StateArray_list(tmp_st,state_list,10);
						
						tmpvar = tmpvar->comparator_out->value_out;
						search = true;
						break;
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
						tmpvar = tmpvar->signal_selector_out->out_signal;
						search=true;
						break;
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
/********************************************end of code *******************************************************/

/**************************************Search_header_of_loop ************************************************/
bool Search_Header_of_loop(State_var *first_state,Path_list*& node,bool search_BasicBlock){

int i=0;
//Path_list *node=NULL;
DeclareData *tmpvar=NULL;
DeclareData *inputs=NULL;
Basic_block *block_ret = NULL;
bool search = false;
DeclareData *arr_tmp[50];

node = new Path_list;
Initialize_array_pointer(node);

while(loop_list[i]){
	search = false;
	if(loop_list[i]->varnode){
		tmpvar = loop_list[i]->varnode;
		if(Search_dominator_of_node(tmpvar,NULL,node,first_state,NULL,false,false,false,search_BasicBlock,block_ret,arr_tmp,NULL)){
			if(Search_dominator_of_node(tmpvar,NULL,node,first_state,NULL,false,true,false,search_BasicBlock,block_ret,arr_tmp,NULL)){
				search = true;
				break;
			}
		}
		else search = false;
	}
	if(!search && loop_list[i]->placenode){
		//search for the node whose output is the rhs_value of the placenode->first_trans_node->data_node->assignment_graph
		if(loop_list[i]->placenode->first_trans_node->data_node->assignment_graph)
			tmpvar = loop_list[i]->placenode->first_trans_node->data_node->assignment_graph->rhs_value;
		else tmpvar = loop_list[i]->placenode->first_trans_node->data_node->condition_op->assign_expr->rhs_value;
		
		if(Search_dominator_of_node(tmpvar,NULL,node,first_state,NULL,false,false,false,search_BasicBlock,block_ret,arr_tmp,NULL)){
			inputs = loop_list[i]->placenode->first_place_input;
			//searching for the other dominators, thus tmpvar should not be checked during this search as it is already searched,thus shouldnt match tmpvar with "inputs"
			while(inputs && strcmp(inputs->name,tmpvar->name)){
				if(Search_dominator_of_node(inputs,NULL,node,first_state,NULL,false,true,false,search_BasicBlock,block_ret,arr_tmp,NULL)){
					search = true;
					break;
				}
				inputs = inputs->next_n;
			}
			if(search) break;
			else if(!search){
				if(Search_dominator_of_node(tmpvar,NULL,node,first_state,NULL,false,true,false,search_BasicBlock,block_ret,arr_tmp,NULL)){
					search = true;
					break;
				}
			}
		}
		else search = false;
	}
	if(!search && loop_list[i]->trannode){
		//in this case, only one output will lead directly to a transition, but more than one node with same output can lead to one trannode
		tmpvar = loop_list[i]->trannode->data_node->assignment_graph->rhs_value;
		if(Search_dominator_of_node(tmpvar,NULL,node,first_state,NULL,false,false,false,search_BasicBlock,block_ret,arr_tmp,NULL)){
			if(Search_dominator_of_node(tmpvar,NULL,node,first_state,NULL,false,true,false,search_BasicBlock,block_ret,arr_tmp,NULL)){
				search = true;
				break;
			}
			else search = false;
		}
	}
	if(!search && loop_list[i]->opnode){
		//here we must search both the inputs of opnode
		tmpvar = loop_list[i]->opnode->op1;
		while(tmpvar){
			if((tmpvar->data_type!= input || tmpvar->data_type!=integer) && Search_dominator_of_node(tmpvar,NULL,node,first_state,NULL,false,false,false,search_BasicBlock,block_ret,arr_tmp,NULL)){
				if(Search_dominator_of_node(tmpvar,NULL,node,first_state,NULL,false,true,false,search_BasicBlock,block_ret,arr_tmp,NULL)){
					search = true;
					break;
				}
				else search = false;
			}
			if(tmpvar == loop_list[i]->opnode->op1)
				tmpvar = loop_list[i]->opnode->op2;
			else tmpvar=NULL;
		}
		if(search) break;
	}
	if(!search && loop_list[i]->eqnode){
		tmpvar = loop_list[i]->eqnode->rhs_value;
		if(Search_dominator_of_node(tmpvar,NULL,node,first_state,NULL,false,false,false,search_BasicBlock,block_ret,arr_tmp,NULL)){
			if(Search_dominator_of_node(tmpvar,NULL,node,first_state,NULL,false,true,false,search_BasicBlock,block_ret,arr_tmp,NULL)){
				search = true;
				break;
			}
			else search = false;
		}
		else search = false;
	}
	// no need of checking comparators and signal selectors, since they do not form part of the loop

	i++;
}

if(!search){
	delete node;node = NULL;
}


return search;

}

/***************************************************** end of code *****************************************************/

/*****************************************Check_loop_body part() *****************************************************/
	if(!control_flow && dataflow && create_loop){
		
		do{
			if(startloop && tmpnode == header_node){		
				node_down=true;
				break;
			}
			startloop = true;
			if(tmpnode->placenode){
				tmpinput = tmpnode->placenode->state_place_input;
				if(!tmpinput) no_state = true;
				while(tmpinput){
					//first check if tmpstate has already been created. iF yes, then tmpstate	
					if(Search_var_from_statelist(tmpinput,tmpstate,false) && Search_state_from_controlnode_list(tmpstate,first_control_node,control_attach)){
						checkstate=true;
						break;
					}
					else tmpinput = tmpinput->next_n;
				}
				//EDITING HERE
				//if there is no state input, then the control inputs to this place,should be output of a control block itself. So first search control blocks if the control input exists, if yes, then insert this basic_block to the child list of control block. if not,
				if(no_state){
					//here check for all the control inputs to the place   tmpstate-garbage variable=NULL
					if(Check_state_of_place_input(tmpnode->placenode,NULL,NULL,tmpnode->placenode->first_trans_node,first_state,tmpstate_list,10,control_attach)){
						checkstate=true;
					}
					else checkstate=false;
				}
				if(checkstate){
					tmpinput = tmpnode->placenode->first_trans_node->data_node->assignment_graph->rhs_value;
					if(Search_end_node_BasicBlock(tmpinput,control_attach->bb_ptr,endnode,controlnode,false,block_ret,false,NULL) || (control_attach->bb_ptr->prev_block && Search_end_node_BasicBlock(tmpinput,first_basic_block,endnode,controlnode,true,block_ret,false,NULL))){
						Create_subnodes_under_endnode(endnode,NULL,controlnode,control_attach->bb_ptr,tmpnode->placenode,block_ret,equalnode,NULL,tmpop,NULL,true,'p');
						first_node = endnode;
						node_down=true;
					}
					else if(Check_parent_nodes(tmpinput,first_state,control_attach,controlnode,endnode,block_ret)){
						node_down=true;
						Create_subnodes_under_endnode(endnode,NULL,controlnode,control_attach->bb_ptr,tmpnode->placenode,block_ret,equalnode,NULL,tmpop,NULL,true,'p');
						first_node = endnode;
					}
						
					else node_down = false;
				}
				else node_down = false;
				
			}
			
			if(!node_down && tmpnode->trannode){
				tmpinput = tmpnode->trannode->data_node->assignment_graph->rhs_value;
					//tmpstate-garbage variable=NULL, check for the state which generated tmpinput 
				if(Check_state_of_place_input(NULL,tmpinput,NULL,NULL,first_state,tmpstate_list,10,control_attach)){
					if(Search_end_node_BasicBlock(tmpinput,control_attach->bb_ptr,endnode,controlnode,false,block_ret,false,NULL) || (control_attach->bb_ptr->prev_block && Search_end_node_BasicBlock(tmpinput,first_basic_block,endnode,controlnode,true,block_ret,false,NULL))){
						Create_subnodes_under_endnode(endnode,NULL,controlnode,control_attach->bb_ptr,NULL,block_ret,equalnode,tmpnode->trannode->data_node->assignment_graph,tmpop,NULL,true,'t');
						first_node = endnode;
						node_down = true;
					}
					else if(Check_parent_nodes(tmpinput,first_state,control_attach,controlnode,endnode,block_ret)){
						node_down=true;
						Create_subnodes_under_endnode(endnode,NULL,controlnode,control_attach->bb_ptr,NULL,block_ret,equalnode,tmpnode->trannode->data_node->assignment_graph,tmpop,NULL,true,'t');		
						first_node = endnode;
					}
					
					else node_down = false;
				}
				else node_down = false;
			}
			if(!node_down && tmpnode->opnode){
				// here u must check if either of the input is connected in which state. 
				//firstcheck if tmpnode is header, then use the node(not part of the loop) which created the header node
				tmpinput = tmpnode->opnode->op1;
				while(tmpinput){
					if(Search_state_of_OperatorInput(first_control_node,tmpnode->opnode,tmpinput,first_state,NULL,controlret)){
					//if(Check_state_of_place_input(NULL,tmpinput,NULL,NULL,first_state,tmpstate_list,10,control_attach)){
						if(Search_end_node_BasicBlock(tmpinput,control_attach->bb_ptr,endnode,controlnode,false,block_ret,false,NULL) || (control_attach->bb_ptr->prev_block && Search_end_node_BasicBlock(tmpinput,first_basic_block,endnode,controlnode,true,block_ret,false,NULL))){
							Create_subnodes_under_endnode(endnode,NULL,controlnode,control_attach->bb_ptr,NULL,block_ret,equalnode,NULL,tmpop,tmpnode->opnode,true,'a');
							node_down=true;
							first_node = endnode;
						}
						else if(Check_parent_nodes(tmpinput,first_state,control_attach,controlnode,endnode,block_ret)){
							node_down=true;
							Create_subnodes_under_endnode(endnode,NULL,controlnode,control_attach->bb_ptr,NULL,block_ret,equalnode,NULL,tmpop,tmpnode->opnode,true,'a');	
							first_node = endnode;				
						}
					}
					if(tmpinput == tmpnode->opnode->op1)
						tmpinput = tmpnode->opnode->op2;
					else tmpinput=NULL;
				}
				
			}
			if(!node_down && (tmpnode->eqnode||tmpnode->dfgnode)){
				if(tmpnode->eqnode)
					tmpinput = tmpnode->eqnode->rhs_value;
				else if(tmpnode->dfgnode){
					if(tmpnode->dfgnode->assignment_graph)
						tmpinput = tmpnode->dfgnode->assignment_graph->rhs_value;
					else {
						//avoid the first condition as it only contains the if_condition for the switch case
						tmpcond = tmpnode->dfgnode->condition_op->next_cond;
						tmpinput = tmpcond->assign_expr->rhs_value;
					}
				}
				//control_attach being returned having the control block
				//if the dfg is a switchcase, then there are mutliple condition_op,nd must be implemented in a loop
				do{
					if(Check_state_of_place_input(NULL,tmpinput,NULL,NULL,first_state,tmpstate_list,10,control_attach)){
						if(Search_end_node_BasicBlock(tmpinput,control_attach->bb_ptr,endnode,controlnode,false,block_ret,false,NULL) || (control_attach->bb_ptr->prev_block && Search_end_node_BasicBlock(tmpinput,first_basic_block,endnode,controlnode,true,block_ret,false,NULL))){
					
							Create_subnodes_under_endnode(endnode,NULL,controlnode,control_attach->bb_ptr,NULL,block_ret,equalnode,tmpnode->eqnode,tmpop,NULL,true,'b');	
							node_down=true;
							first_node = endnode;
						}
						else if(Check_parent_nodes(tmpinput,first_state,control_attach,controlnode,endnode,block_ret)){
							node_down=true;
							Create_subnodes_under_endnode(endnode,NULL,controlnode,control_attach->bb_ptr,NULL,block_ret,equalnode,tmpnode->eqnode,tmpop,NULL,true,'b');	
							first_node = endnode;
						}
						else node_down=true;
					}
					else node_down = false;
					
					if(tmpcond){
						tmpcond = tmpcond->next_cond;
						tmpinput = tmpcond->assign_expr->rhs_value;
					}
				}while(tmpinput);
			
			}
			
			if(node_down){
				tmpnode = loop_list[i];
				startloop = false;
				i++;
		
			}
			
			
		}while(tmpnode);	
	}

/**********************************************************end of code ************************************************************************/




