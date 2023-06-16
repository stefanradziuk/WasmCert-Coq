#use "itp_extr.ml";;

let time f x =
  let t = Sys.time() in
  let fx = f x in
  Printf.printf "execution time: %fs\n" (Sys.time() -. t);
  fx;;

let cl2s cl = String.concat "" (List.map (String.make 1) cl);;

let n = Extr.n_(*n*);;

let fib = Extr.fib n;;
let fuel = Extr.fuel_fib n;;

let interpret_partially_applied = Extr.run_v_wrap fuel Extr.depth Extr.emp_store_record Extr.loc_frame;;

let res = time interpret_partially_applied fib;;

let ppstr = cl2s (Extr.pp_res_val res);;

let () = print_endline ppstr;;

