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


(*>* Problem 2.1 *>*)

(* evaluate : evaluates an expression for a particular value of x. 
 *  Example : evaluate (parse "x*x + 3") 2.0 = 7.0 *)
let rec evaluate (e:expression) (x:float) : float =
  failwith "Not implemented" 



(*>* Problem 2.2 *>*)

(* See writeup for instructions.  *)
let rec derivative (e:expression) : expression =
  failwith "Not implemented"



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


(*>* Problem 2.3 *>*)

(* See writeup for instructions. *)
let rec find_zero (e:expression) (g:float) (epsilon:float) (lim:int)
    : float option =
  failwith "Not implemented" 



(*>* Problem 2.4 *>*)

(* See writeup for instructions. *)
let rec find_zero_exact (e:expression) : expression option =
  failwith "Not implemented" 

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
