
//control_st should be passed tothe Check_loop_body in the beginning
//startloop becomes false after the first iteration of the do-while loop
if(!control_flow && dataflow && create_loop){

	//num++;
	first_node = new Path_list;
	Initialize_array_pointer(first_node);
	Search_header_in_loop(header_node,startnode,nextnode,false,i);
	startloop = true;
	do{
		if(startloop)
			//search for the loop_list node which is the header_node and return the index "i"
			Search_node_in_Looplist(header_node,nodenull,nextnode,true,i);
			
		//startloop = false;
		if(loop_list[i]->placenode){
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
					}
					while(tmpvar){
						if(strcmp(tmpvar->name , temp->name)){
							if(tmpvar->unary_operator || Search_var_from_graph(tmpvar,NULL,NULL,prev_comp,prev_signal,NULL,first_state,false,true)){
								if(Search_control_nodes(NULL, controlnode ,endnode, tmpvar,NULL)){
									if(prev_comp)
										Create_control_node(tmp_control,endnode,prev_comp,control_st,first_state,controlnode,NULL,NULL,tmpeq,true);
									else if(prev_signal)
										Create_control_node(tmp_control,endnode,NULL,control_st,first_state,controlnode,prev_signal,NULL,tmpeq,true);
									statecheck=true;
								}
							}
						}
						if(!statecheck) tmpvar = tmpvar->next_n;
					}
				}
				
					if(!startloop){
						endnode = tmp_prev;
						controlnode = tmp_control;
						control_st = controlnode;
					}
						
					else if(startloop && Search_end_node_BasicBlock(depth_tmp , first_basic_block ,endnode,controlnode,true, block_ret,false,NULL))
						controlnode = control_st;
					
						tmpeq = NULL;
						Create_subnodes_under_endnode(endnode ,NULL,controlnode,basicblock_loop,tmp_place,blocknull,tmpeq,NULL,tmpop,NULL,true, 'p');
						tmp_prev = tmpeq->lhs_value;
						//node_down = true;
						if(!tmp_control->bb_ptr) tmp_control->bb_ptr = block_ret;
						Insert_in_BasicBlock_array(block_ret->control_node_pointers,10,tmp_control);
				
				
			//check for the state input if its there ,and if yes, then search from control list and attach it to the 
		}
		else if(loop_list[i]->eqnode){
			if(!startloop){
				endnode = tmp_prev;
				controlnode = control_loop;
				control_st = controlnode;
			}
			//occurs only one time
			else if(startloop && Search_end_node_BasicBlock(varsearch,first_basic_block,endnode,controlnode,true,block_ret,false,NULL))
				controlnode = control_st;
				
			tmpeq = NULL;
			Create_subnodes_under_endnode(endnode,varsearch,controlnode,basicblock_loop,NULL,blocknull,tmpeq,loop_list[i]->eqnode,tmpop,NULL,true,'b');
			tmp_prev = tmpeq->lhs_value;
			if(startloop) flag = true;
		}
		else if(loop_list[i]->trannode){
			if(!startloop){
				endnode = tmp_prev;
				controlnode = control_loop;
				control_st = controlnode;
			}
			else if(startloop && Search_end_node_BasicBlock(varsearch,first_basic_block,endnode,controlnode,true,block_ret,false,NULL))
				controlnode = control_st;
				
			equalnode = loop_list[i]->trannode->data_node->assignment_graph;
			tmpeq = NULL;
			Create_subnodes_under_endnode(endnode,varsearch,controlnode,basicblock_loop,NULL,blocknull,tmpeq,equalnode,tmpop,NULL,true,'t');
			tmp_prev = tmpeq->lhs_value;
			if(startloop) flag = true;
		}
		else if(loop_list[i]->opnode){
			//check forthe input which is not part of the loop.
			if(!startloop){
				endnode = tmp_prev;
				controlnode = control_loop;
				control_st = controlnode;
			}
			else if(startloop && Search_end_node_BasicBlock(varsearch,first_basic_block,endnode,controlnode,true,block_ret,false,NULL))
				controlnode = control_st;
				
			tmpvar = loop_list[i]->opnode->op1;
			//search for the other input- tmpvar
			while(tmpvar){
				if(!strcmp(varsearch-name, tmpvar->name))
					continue;
				else break;
				if(tmpvar == loop_list[i]->opnode->op1)
					tmpvar = loop_list[i]->opnode->op2;
				else tmpvar = NULL;
			}
			if(tmpvar && Search_end_node_BasicBlock(tmpvar,first_basic_block,endnode_tmp,controlnode_tmp,true,blocknull,false,NULL)){
				//here blocknull contains the basicblock which contains tmpvar
				//check if the operator is connected from endnode
				if(endnode_tmp->operator_out){
					opcreate = false;
					tmpop = endnode_tmp->operator_out;
					if(endnode_tmp->operator_out->op1)
						endnode_tmp->operator_out->op2 = endnode;
					else endnode_tmp->operator_out->op1 = endnode;
				}
				//else store the other input in endnode_tmp itself
			}
			else opcreate = true;
			tmpop = NULL;
			//if both tmpvar and varsearch are in same block, then no need to send thru blocknull
			if(basicblock_loop == blocknull)
				blocknull = NULL;
			//else blocknull will have the block which has tmpvar
			if(opcreate)
				Create_subnodes_under_endnode(endnode,varsearch,controlnode,basicblock_loop,NULL,blocknull,tmpeq,NULL,tmpop,loop_list[i]->opnode,false,'a');
			tmp_prev = tmpop->output_value;
			if(startloop) flag = true;
				
		}
		if(flag){
			startloop = false;
			flag = false;
			if(tmpeq) first_node->eqnode = tmpeq;
			else if(tmpop) first_node->opnode = tmpop;
		}
		else i--;
		
	}while(i > 1);

	Attach_first_node_in_Loop(tmp_prev , first_node);
	delete first_node;
	first_node = NULL;


}

if(!flag){
	delete_loop_list();
}







