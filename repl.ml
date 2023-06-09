#use "progress_extracted.ml";;

let time f x =
  let t = Sys.time() in
  let fx = f x in
  Printf.printf "execution time: %fs\n" (Sys.time() -. t);
  fx;;

let cl2s cl = String.concat "" (List.map (String.make 1) cl);;

let interpret_partially_applied = ProgressExtract.interpret_multi_step
  ProgressExtract.fuel_fib
  ProgressExtract.emp_store_record
  ProgressExtract.loc_frame
  ProgressExtract.fib
  ProgressExtract.ts_fib
  (Obj.magic ProgressExtract.host_eqType);;

let e' = time
  interpret_partially_applied
  ProgressExtract.coq_H_config_typing_fib;;

let ppstr = cl2s (ProgressExtract.pp_head_val e');;

let () = print_endline ppstr;;

