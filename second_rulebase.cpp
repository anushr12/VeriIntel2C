#include <iostream>
#include <new>
#include <stdio.h>
#include <string.h>
#include <DFG_transform.h>
//input CDFG:
//ASSUMPTION: only the control loop blocks and the BB containing the loop body statements and list of temporary variables and list of array variables in separate lists

using namespace std;

void second_rulebase(DeclareData *varlist,Control_block *first_control_node,Basic_block *first_basic_block, Array_list *oneD_array, Array_list *twoD_array){


//carry out rule1- to fix data types int,char
//next carry out rule2 - to merge arrays and modify loops

if(twoD_array){
	//Search largest 2D array
	if(Search_largest_array(twoD_array,start_arr)){
		//if array is homogenous
		//start_arr is the base array to start from
		if(start_arr->row_ind == start_arr->col_ind){
			tmp = oneD_array;
			for(tmp = oneD_array;tmp!=NULL;tmp=tmp->next_arr){
				if(tmp->index == start_arr->row_ind){
					Insert_row_in_Array(start_arr,tmp);
					start_arr->row_ind++;
					Modify_loop_of_array(start_arr,twoD_array,tmp,first_basic_block,first_control_node);
				}
			}
			Delete_array(twoD_array,start_arr,NULL,true);	
			
			
		}
		else if(Check_array_homogenous(oneD_array,homo_arr)){
			//if base array is non homogenous
			Calculate_index(twoD_array,homo_arr,total_index);
			//search a row-col pair
			if(Search_pair(total_index,homo_arr,row,col)){
				for(tmp=homo_arr ; tmp!=NULL; tmp = tmp->next_arr){
					
					 
					row=0;col=0;
					
					if(row && tmp->index == row){
						Insert_row_in_Array(start_arr,tmp,true);
						start_arr->row_ind++;
						done = true;
					}
					else if(col && tmp->index == col){
						Insert_row_in_Array(start_arr,tmp,false);
						start_arr->col_ind++;
						done = true;
					}
					if(done == true)
					Modify_loop_of_array(start_arr,twoD_array,tmp,first_basic_block,first_control_node);
				}
				Delete_arrays(NULL,NULL,homo_arr,false);
			}
		}
		
	}
	
}
else if(oneD_array->next_arr){
	//if no two dimensional arrays are found and more than 1D array is found	
	Calculate_index(NULL,oneD_array,total_index);
	// to search a row-col pair to include all 1d arrays
	// check_array_homo to get all homogenous 1d arrays which are same in size
	if(Search_pair(total_index,oneD_array,row,col) && Check_array_homogenous(oneD_array,homo_arr)){
		new_2D_arr = new Array_list;
		Initialize_array(new_2D_arr);
		new_2D_arr->row_ind = row; new_2D_arr->col_ind = col;
		for(tmp = homo_arr; tmp!=NULL; tmp=tmp->next_arr){
			row=0;col=0;
			Insert_row_in_Array(new_2D_arr,tmp,true);
			Modify_loop_of_array(new_2D_arr,NULL,tmp,first_basic_block,first_control_node);
		}
		Delete_arrays(NULL,NULL,homo_arr,false);
	}
		

}

}


//fn to modify the loops of arrays, if twoD_arr list exists, or even when only 1D arrays exist
void Modify_loop_of_array(Array_list *base2D_arr,Array_list *twoD_arr, Array_list *one_arr, Basic_block *first_basic_block, Control_block *first_control_node){

Array_list *tmp_arr;
Control_block *tmp = NULL;
Path_list *exit_node = NULL;

//Search the control loops for exit points
for(tmp = first_control_node;tmp!=NULL; tmp = tmp->next_control_block){
	//condition to check for a control loop
	if(tmp->control_dfg_node && tmp->control_dfg_node->assignment_graph || tmp->control_dfg_node->operation_graph){
		i=0;
		while(i<2){
			if(i==0)
				tmp_n = one_arr;
			else tmp_n = twoD_arr;
			while(tmp_n){
				if(Search_exit_point(tmp->control_dfg_node,exit_node,tmp_n)){
					if(Search_control_index(tmp->control_dfg_node,index) && index==base2D_arr->row_ind | base2D_arr->col_ind)
					Modify_body(tmp_n,base2D_arr,base2D_arr->row_ind,base2D_arr->col_ind);
			
				}
				tmp_n = tmp_n->next_arr;
			
			}
		//	tmp_n = twoD_arr;
		}


	}


}


}


void Modify_body(Array_list *arr_replace, Array_list*& 2D_arr_new,int row, int col){

int i=0;
Array_list *tmp;

//to check if the array to replace is 1d or 2d
if(!arr_replace->twodim_var){
	tmp[i] = 2D_arr_new->twodim_var;
	while(tmp[i]){
		if(*tmp[i] == *arr_replace){
			if(row == arr_replace->index){
				arr_replace = 2D_arr_new;
				arr_replace->row_ind = *tmp[i]->index;
			}
			else if(col == arr_replace->index){
				arr_replace = 2D_arr_new;
				arr_replace->col_ind = *tmp[i]->index;
			}
		}

	}

}
//if it is 2D arrray
else{
	
	


}




}











//fn to search largest amongst all the 2D arrays in twodim
bool Search_largest_array(Array_list *twodim,Array_list*& largest_arr){

//check if indexes multiplied together is the highest
int index;
bool flag=false;
Array_list *tmp;

if(!twodim->next_arr){
	largest_arr = twodim;
	flag = false;

}


for(tmp = twodim; tmp!=NULL; tmp=tmp->next_arr){
	index = tmp->row_ind * tmp->col_ind;
	if(!tmp->prev_arr){
		largest_arr = tmp;
		largest_ind = index;
	}
	else if(index > largest_ind){
		largest_ind = index;
		largest_arr = tmp;
	}
	
}

if(largest_ind)
	flag = true;
else
	flag = false;

return flag;

}


//fn to delete the oned arraylist if search is false or 2d arraylist if search is true and delete those arrays which is not array_selected
void Delete_arrays(Array_list*& twodim_list, Array_list *array_selected, Array_list *onedim_list, bool search){

Array_list *tmp;

if(search){
	for(tmp = twodim_list;tmp!=NULL;tmp=tmp->next_arr){
		if(tmp != array_selected){
			if(!tmp->prev_arr){
				tmp->next_arr->prev_arr = NULL;
				tmp->next_arr->next_arr = tmp->next_arr;
			}
			else if(!tmp->next_arr){
				tmp->prev_arr->next_arr = NULL;
				tmp->prev_arr->prev_arr = tmp->prev_arr;
			}
			else{
				tmp->prev_arr->next_arr = tmp->next_arr;
				tmp->next_arr->prev_arr = tmp->prev_arr;
			}
			//its two dimensional so delete the row arrays first
			Delete_sub_arrays(tmp);
			delete tmp;
			tmp = NULL;
		}

	}
}
else{
	for(tmp = onedim_list;tmp!=NULL; tmp = tmp->next_arr){
		
			if(!tmp->prev_arr){
				tmp->next_arr->prev_arr = NULL;
				tmp->next_arr->next_arr = tmp->next_arr;
			}
			else if(!tmp->next_arr){
				tmp->prev_arr->next_arr = NULL;
				tmp->prev_arr->prev_arr = tmp->prev_arr;
			}
			else{
				tmp->prev_arr->next_arr = tmp->next_arr;
				tmp->next_arr->prev_arr = tmp->prev_arr;
			}
			delete tmp;
			tmp = NULL;

	}
}


}











