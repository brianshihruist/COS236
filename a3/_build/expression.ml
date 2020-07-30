(* 

Name:
Email:
Minutes Spent on the for-credit parts of Problem 2:

(You aren't in any way graded on the number of minutes spent; 
 we are just trying to calibrate for future versions of the class)

Comments/Problems/Thoughts on this part of the assignment:

*)

open Ast 
open ExpressionLibrary 

(* TIPS FOR PROBLEM 2:
 * 1. Read the writeup.
 * 2. Use the type definitions in the ast.ml as a reference. But don't worry 
 *    about expressionLibrary.ml
 * 3. Test!  (Use "assert" where appropriate.)
 *)
let map : ('a -> 'b) -> 'a list -> 'b list = List.map

let filter : ('a -> bool) -> 'a list -> 'a list = List.filter

let foldr : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b = List.fold_right

let foldl : ('b -> 'a -> 'b) -> 'b -> 'a list -> 'b = List.fold_left

(*>* Problem 2.1 *>*)

(* evaluate : evaluates an expression for a particular value of x. 
 *  Example : evaluate (parse "x*x + 3") 2.0 = 7.0 *)
let rec evaluate (e:expression) (x:float) : float =
  match e with
  | Num n -> n
  | Var -> x
  | Binop (binop, exp1, exp2) -> 
    let e1 = evaluate exp1 x in
    let e2 = evaluate exp2 x in
    match binop with
    | Add -> e1 +. e2
    | Sub -> e1 +. e2
    | Mul -> e1 *. e2


let _ = assert ( evaluate (parse "x*x + 3") 2.0 = 7.0 )

(*>* Problem 2.2 *>*)

(* derivative(f + g)(x) = derivative(f)(x) + derivative(g)(x)
derivative(f - g)(x) = derivative(f)(x) - derivative(g)(x)
derivative(f * g)(x) = derivative(f)(x) * g(x) + f(x) * derivative(g)(x) *)

(* See writeup for instructions.  *)
let rec derivative (e:expression) : expression =
  match e with
  | Num n -> Num 0.
  | Var -> Num 1.
  | Binop (binop, exp1, exp2) -> 
    let d_e1 = derivative exp1 in
    let d_e2 = derivative exp2 in
    match binop with
    | Add -> Binop(Add, d_e1, d_e2)
    | Sub -> Binop(Sub, d_e1, d_e2)
    | Mul -> Binop(Add, Binop(Mul, d_e1, exp2 ), Binop(Mul, d_e2, exp1))


(* A helpful function for testing. See the writeup. *)
let checkexp strs xval=
  print_string ("Checking expression: " ^ strs^"\n");
  let parsed = parse strs in (
	print_string "Result of evaluation: ";
	print_float  (evaluate parsed xval);
	print_endline " ";
	print_string "Result of derivative: ";
	print_endline " ";
	print_string (to_string (derivative parsed));
	print_endline " ")

let _ = checkexp "x*x + 3*x" 2.

(*>* Problem 2.3 *>*)

(* See writeup for instructions. *)
let rec find_zero (e:expression) (g:float) (epsilon:float) (lim:int)
    : float option =
    if lim = 0 
      then None
    else if (abs_float g < epsilon) 
      then Some g
    else let new_g = g -. (evaluate e g) /. (evaluate (derivative e) g )
    in find_zero e new_g epsilon (lim - 1);;



(*>* Problem 2.4 *>*)

(* simplifyList
evaluateToList *)
type coefficient = float
type power = int
type sym_unit = coefficient * power

let rec simplify_list (lst: sym_unit list) =
  let sum_coefficient (power: int) (symUnits: sym_unit list): float =
    foldl (fun n (c, p) -> if p = power then n +. c else n ) 0. symUnits in
  let filter_out_power (power: int) (symUnits: sym_unit list): sym_unit list =
    foldl (fun lst (c, p) -> if p = power then lst else (c, p)::lst) [] symUnits in
  match lst with
  | [] -> []
  | (c, p)::t -> let newCo = sum_coefficient p (lst) in
                 (newCo, p):: simplify_list (filter_out_power p t);;
    

let rec print_sym_list (lst: sym_unit list) =
  match lst with
  | [] -> 0
  | (c, p):: t ->
    print_float c;
    print_string ",";
    print_int p;
    print_string "\n";
    print_sym_list t;;

(* let _ = print_sym_list (simplify_list [(3.1, 2); (3.1, 10); (3.1, 2)]);; *)

let _ = assert(simplify_list [(3.1, 2); (3.1, 10); (3.1, 2)] = [(6.2, 2); (3.1,10)]);;


let rec construct_simple_list (e: expression): sym_unit list =
  let multiply_lists (l1: sym_unit list) (l2: sym_unit list): sym_unit list =
    foldl (fun acc (c1, p1) -> acc @ map (fun (c2, p2) -> (c1 *. c2, p1 + p2)) l2) [] l1
    in
  let remove_zero_coefficient (lst: sym_unit list): sym_unit list =
    foldl (fun acc (c, p) -> if c = 0. then acc else (c,p)::acc) [] lst in
  let res = match e with
  | Num n -> [ (n, 0) ]
  | Var -> [ (1., 1) ]
  | Binop (binop, exp1, exp2) -> 
    let l1 = construct_simple_list exp1 in
    let l2 = construct_simple_list exp2 in
    match binop with
      | Add -> l1 @ l2
      | Sub -> l1 @ (map (fun (c,p) -> (~-.c, p)) l2)
      | Mul -> multiply_lists l1 l2
    in remove_zero_coefficient res;;
        
(* let _ = print_sym_list (construct_simple_list (parse "x*x + 2 + 2*x"));; *)


(* See writeup for instructions. *)
let rec find_zero_exact (e:expression) : expression option =
  let simple_list = construct_simple_list e in
  let size = List.length  simple_list in
  match size with
  | 0 -> None
  | 2 -> (match simple_list with
    | [(c1, b1); (c2, b2)] -> None
    | _ -> None)
  | _ -> None
  

(* For extra fun (but not extra credit),
  implement find_zero_exact2 that solves degree-two expressions.
  This is almost as easy as solving degree-one expressions,
  if you use the quadratic formula.  Almost as easy, assuming
  you've already done the work to normalize polynomials into an
  easily recognizable form. *)


(* For extra fun (but not extra credit), 

 Consider this function,
  let evaluate2 (e: expression) : float -> float =
     let e' = derivative e in
     fun x -> (evaluate e x, evaluate e' x)

 Such a function can be used in Newton's method.
 But if the expression e is large, e' can be exponentially larger,
 because of the chain rule for multiplication, so
 evaluate e' x  can be slow.

 One solution is called "forward mode automatic differentiation",
 which has become an important algorithm (since 2017 or so) in
 deep learning.  You can read about it in section 3.1 of
 this paper:  http://jmlr.org/papers/volume18/17-468/17-468.pdf
 "Automatic Differentiation in Machine Learning: A Survey"
 (and pay particular attention to Table 2 for a worked example).

 So, the challenge (which is actually not very difficult) is,
 write this function

  let evaluate2 (e: expression) (x: float) : float * float = ...

 that computes both e(x) and the first derivative e'(x),
 without ever calculating (derivative e).  Like evaluate,
 do it by case analysis on the syntax-tree of e. *)
	   
(* Q.  Why do it, if no extra credit?
   A.  Because (and only if) it's fun.  
   A.  Because the main reason you're working so hard at Princeton
       is to learn things, not just to get grades.
   A.  Any well educated computer scientist graduating after 2019
     ought to know something about deep learning . . .
 *)
