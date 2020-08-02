(*************************************************)
(* An environment-based evaluator for Dynamic ML *)
(*************************************************)

open Syntax
open Printing
open EvalUtil

(* Defines the subset of expressions considered values
   Notice that closures are values but the rec form is not -- this is
   slightly different from the way values are defined in the 
   substitution-based interpreter.  Rhetorical question:  Why is that?
   Notice also that Cons(v1,v2) is a value (if v1 and v2 are both values).
*) 
let rec is_value (e:exp) : bool = 
  match e with
      Constant _ -> true  
    | Pair (e1, e2) -> is_value e1 && is_value e2
    | EmptyList -> true
    | Cons (e1, e2) -> is_value e1 && is_value e2
    | Closure _ -> true
    | _ -> false

(* evaluation; use eval_loop to recursively evaluate subexpressions *)
let eval_body (env:env) (eval_loop:env -> exp -> exp) (e:exp) : exp = 
  match e with
    | Var x -> 
      (match lookup_env env x with 
  	  | None -> raise (UnboundVariable x)
	    | Some v -> v)
    | App (e1, e2) -> (
      let arg_value = eval_loop env e2 in
      match eval_loop env e1 with
      | (Rec (f,x,body)) as recf -> (
        let body_env = update_env env x arg_value in
        eval_loop body_env body
      )
      | Closure (closure_env,f,x,b) -> (
        let body_env = update_env closure_env x arg_value in
        eval_loop body_env body
      )
      | v1 -> raise (BadApplication v1)
    )
    | Let (y, e1, e2) -> (
      let bind_value = eval_loop env e1 in
      match bind_value with
      | (Rec (f, x, b)) as recf ->
        let closure_env = update_env env y Closure (env,f,x,b) in
        eval_loop closure_env e2
      | _ ->  eval_loop (update_env env y bind_value) e2
    )
    | Rec (f, y, e1) -> failwith "haven't implemented Rec"
    | Match (e1, e2, hd, tl, e3) -> failwith "haven't implemented Match"
    | Constant _ -> failwith "haven't implemented Constant"
    | Op -> failwith "haven't implemented Op"
    | If -> failwith "haven't implemented If"
    | _ -> failwith "unimplemented"

(* evaluate closed, top-level expression e *)

let eval e =
  let rec loop env e = eval_body env loop e in
  loop empty_env e


(* print out subexpression after each step of evaluation *)
let debug_eval e = 
  let rec loop env e =
    if is_value e then e  (* don't print values *)
    else 
      begin
	Printf.printf "Evaluating %s\n" (string_of_exp e); 
	let v = eval_body env loop e in 
	Printf.printf 
	  "%s evaluated to %s\n" (string_of_exp e) (string_of_exp v); 
	v
      end
  in
  loop empty_env e
