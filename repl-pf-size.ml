#use "progress_extracted.ml";;

let res = ProgressExtract.interpret_multi_step_pf ProgressExtract.fuel_fib ProgressExtract.emp_store_record ProgressExtract.loc_frame ProgressExtract.fib ProgressExtract.ts_fib (Obj.magic ProgressExtract.host_eqType) ProgressExtract.coq_H_config_typing_fib;;

let pf = match res with | ExistT (_, ExistT (_, ExistT (_, res'))) -> res';;

#print_length 999999;;
#print_depth 999999;;

pf;;

