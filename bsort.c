/*******************************************************************************/
/* bsort block                                       2009.05.22  A.Yamashiroya */
/*                                       kaizou      2009.06.04                */
/*******************************************************************************/

/* from fifocnt1        */

in  var(0..0) bb_ffo1_ok  ; // input data cnt fifo1 valid

/* from bb_ffo2_ok      */

in  var(0..0) bb_ffo2_ok  ; // input data cnt fifo2 valid

/* to fifocnt1          */

//out var(0..0) bb_cnt1_v   ; // input data fifo1 RD end validl
out var(7..0) bb_cnt1_d   ; // input data cnt

/* to fifocnt2          */

//out var(0..0) bb_cnt2_v   ; // output data cnt WR confirm validl
out var(7..0) bb_cnt2_d   ; // output data cnt 
//out var(0..0) bb_cnt2_end ; // output data fifo2 WR end 

/* shared memory -> input,output pin */

in  ter(7..0) smem_cnt1 ;
in  ter(7..0) smem_dt1 ;
out ter(7..0) smem_cnt2 ;
out ter(7..0) smem_dt2 ;


process bsort(){
	
	reg(7..0) array[256] ;
	var(7..0) b_cnt ,num ,bbi ,bbj ,temp ;
	
	/*while(1){
		if(input(bb_ffo1_ok) ==1) break ;
	}*/
	
	b_cnt = smem_cnt1 ;
	
	for(num=0;num<b_cnt;num++){
		array[num] = smem_dt1 ;
	}
	/*
	wait(1){
		bb_cnt1_v = 1 ;
		output(bb_cnt1_v) ;
		bb_cnt1_d = b_cnt ;
		output(bb_cnt1_d) ;
	}
	wait(1){
		bb_cnt1_v = 0 ;
		output(bb_cnt1_v) ;
	}*/
	
	/* bubule sort */
	
	for(bbi = 0 ; bbi < b_cnt ; bbi++){
		for(bbj = b_cnt - 1 ; bbj > bbi ; bbj--){
			if(array[bbj] < array[bbj-1]){
				temp         = array[bbj] ;
				array[bbj]   = array[bbj-1] ;
				array[bbj-1] = temp ;
			}
		}
	}
	bb_cnt2_d = b_cnt ;
	output(bb_cnt2_d) ;
	/*
	wait(1){
		bb_cnt2_v = 1 ;
		output(bb_cnt2_v) ;
		bb_cnt2_d = b_cnt ;
		output(bb_cnt2_d) ;
	}*/
	/*
	while(1){
		if(input(bb_ffo2_ok) ==1) break ;
	}*/
	/*
	wait(1){
		bb_cnt2_v = 0 ;
		output(bb_cnt2_v) ;
	}*/
	smem_cnt2 = b_cnt ;
	
	for(num=0;num<b_cnt;num++){
		smem_dt2 = array[num] ;
	}
	//wait(1) ;
	//bb_cnt2_end = 1 ;
	//output(bb_cnt2_end) ;
	//wait(1)
	//bb_cnt2_end = 0 ;
	//output(bb_cnt2_end) ;
}
