(* 

Name:
Netid:
Minutes Spent on Problem 1.1:
Minutes Spent on Problem 1.2:

(You aren't in any way graded on the number of minutes spent; 
 we are just trying to calibrate for future versions of the class)

Comments/Problems/Thoughts on this part of the assignment:

*)

(* This part of the assignment uses the following functions 
 * If you forget how they work, look them up:
 * http://caml.inria.fr/pub/docs/manual-ocaml/libref/List.html
 *)

 let print_list f lst =
  let rec print_elements = function
    | [] -> ()
    | h::t -> f h; print_string ";"; print_elements t
  in
  print_string "[";
  print_elements lst;
  print_string "]";
  print_string "\n"
;;

let print_int_list = print_list print_int;;
let print_string_list = print_list print_string;;


let map : ('a -> 'b) -> 'a list -> 'b list = List.map

let filter : ('a -> bool) -> 'a list -> 'a list = List.filter

let foldr : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b = List.fold_right

let foldl : ('b -> 'a -> 'b) -> 'b -> 'a list -> 'b = List.fold_left

(* reduce is equivalent to List.fold_right, 
 * only its args are ordered differently *)
let rec reduce (f:'a -> 'b -> 'b) (u:'b) (xs:'a list) : 'b =
  match xs with
    | [] -> u
    | hd::tl -> f hd (reduce f u tl) 

(***********************************************)
(******            1.1 WARM UP            ******)
(***********************************************)

(* Solve each problem in this part using map, reduce, foldl, foldr or
 * filter.  Map, filter, reduce, foldl, foldr are an example of a
 * *combinator library*: a library of higher-order functions used to
 * solve problems in a particular domain.  In this case, the domain is
 * list-processing.  However, there are countless other useful
 * combinator libraries.  The goal is to get used to thinking about how
 * to decompose complex functions in to smaller, simpler, orthogonal
 * functional components.  The smaller, simpler functional components
 * can be constructed directly using the combinator library.
 * 
 * Note: foldl is slightly more efficient than foldr because it is tail
 * recursive.  (We will explain what that means later in the course.)
 * Hence, solutions that use foldl are typically superior to solutions
 * that use foldr, all other things being equal.  Thus you should try
 * to use foldl where you can instead of foldr (but take care to retain
 * good style -- a horribly convoluted, incomprehensible function that
 * uses foldl is worse than an elegant one that uses foldr).
 * 
 * In these problems, you are not allowed to use the "rec" keyword in
 * your solution.  A solution, even a working one, that uses explicit
 * recursion via "rec" will receive little to no credit.  You may write
 * useful auxiliary functions; they just may not be recursive.  
 * (The goal of this part of the assignment is not to simulate
 * everyday programming.  It is to get you think about writing programs
 * in a different style from what you are used to.  We are trying to
 * enlarge your programming toolkit.)
 * 
 * You are also not allowed to use other functions from a standard or
 * external library such as sort, concat or flatten, nor the built-in
 * list operator @.  (You are allowed to recode those functions
 * yourself using map, filter, fold if you find it necessary.)
 * 
 *)

(*>* Problem 1.1.a *>*)

(*  negate_all : Flips the sign of each element in a list *)
let negate_all (nums:int list) : int list =
  map (fun x -> ~-x) nums;;


(* Unit test example.  Uncomment after writing negate_all *)
let _ = assert ((negate_all [1; -2; 0]) = [-1; 2; 0])


(*>* Problem 1.1.b *>*)

(*  sum_rows : Takes a list of int lists (call an internal list a "row").
 *             Returns a one-dimensional list of ints, each int equal to the
 *             sum of the corresponding row in the input.
 *   Example : sum_rows [[1;2]; [3;4]] = [3; 7] *)
let sum_rows (rows:int list list) : int list =
  let add_list = foldl (fun acc ele -> acc + ele) 0 in
  map add_list rows;;

let _ = assert ((sum_rows [[1;2]; [3;4]]) = [3; 7])

(*>* Problem 1.1.c *>*)

(*  num_occurs : Returns the number of times a given number appears in a list.
 *     Example : num_occurs 4 [1;3;4;5;4] = 2 *)
let num_occurs (n:int) (nums:int list) : int =
  foldl (fun acc ele -> if ele = n then acc + 1 else acc) 0 nums;;

let _ = assert (num_occurs 4 [1;3;4;5;4] = 2)

(*>* Problem 1.1.d *>*)

(*  super_sum : Sums all of the numbers in a list of int lists
 *    Example : super_sum [[1;2;3];[];[5]] = 11 *)
let super_sum (nlists:int list list) : int =
  let sum = foldl (+) 0 in
  sum (map ( fun lst -> sum lst ) nlists);;

let _ = assert (super_sum [[1;2;3];[];[5]] = 11)

(****************************************************)
(**********       1.2 A Bigger Challenge   **********)
(****************************************************)

(* Note: some of these questions may be challenging. Don't neglect
 * Part 2 of this assignment because you are working on these problems.
 * 
 * Again, these problems should be solved using a higher-order function
 * -- we intend that you use one or more folds, though map and filter
 * are acceptable if you find them useful -- and very little to no
 * credit will be given for doing them with explicit recursion. 
 *
 *)


(*>* Problem 1.2.a *>*)

(* consec_dedupe : removes consecutive duplicate values from a list.
 * More specifically, consec_dedupe has two arguments: 
 *   eq is a function representing an equivalence relation 
 *   xs is a list of elements.  
 * It returns a list containing the same elements as lst, but without 
 * any consecutive duplicates, where two elements are considered 
 * duplicates if applying eq to them yields true.
 * 
 * Example: consec_dedupe (=) [1; 1; 1; 3; 4; 4; 3] = [1; 3; 4; 3].
 * 
 * Example:
 * 
 * let nocase_eq (s1:string) (s2:string) : bool = (String.uppercase s1)
 * = (String.uppercase s2) 
 * 
 * consec_dedupe nocase_eq ["hi"; "HI"; "bi"] = ["hi"; "bi"]
 * 
 * (When consecutive duplicates are not exactly syntactically equal, as
 * above, it does not matter which of the duplicates are discarded.)
 * 
 *)

let consec_dedupe (eq:'a -> 'a -> bool) (xs:'a list) : 'a list =
  let remove_dup first lst = foldr (fun ele (curr_num, curr_list) -> 
                            if eq curr_num ele
                              then (curr_num, curr_list)
                              else (ele, ele::curr_list))
                              lst
                              (first, [])
                             in
  match xs with
  | [] -> []
  | h::t -> let (a,b) =  remove_dup h (h::t) in b;;

let nocase_eq (s1:string) (s2:string) : bool = (String.uppercase_ascii s1) = (String.uppercase_ascii s2) 
(* let _ = print_string_list (consec_dedupe nocase_eq ["hi"; "HI"; "bi"]);; *)
let _ = assert (consec_dedupe nocase_eq ["hi"; "HI"; "bi"] = ["HI"; "bi"])
(* let _ = print_int_list (consec_dedupe (=) [1;2;2;3;4;2;2;4;4]);; *)

let _ = assert (consec_dedupe (=) [1;2;2;3;4;2;2;4;4] = [1;2;3;4;2;4])



(*>* Problem 1.2.b *>*)

(* prefixes: return a list of all non-empty prefixes of a list, 
 * ordered from shortest to longest.
 * 
 * Example: prefixes [1;2;3;4] = [[1]; [1;2]; [1;2;3]; [1;2;3;4]].
 * 
 * There are no non-empty prefixes of an empty list.
*)

(* let prefixes (xs: 'a list) : 'a list list =
  let take_helper n lst = foldl 
    (fun (count, arr) ele -> if count >= n then (count+1, arr) else (count+1, ele::arr))
    (0, []) lst in
    
  let number_seq lst = foldl 
    ( fun (n, arr) ele -> (n+1, n+1::arr)) (0, []) lst  in

    let map_seq listy = let (a,b) = (number_seq listy) in b in

    let take n lst = let (a,b) = take_helper n lst in a in

    map (fun a -> take a xs) (map_seq xs);; *)






(*>* Problem 1.2.c *>*)
(* flatten : write a function that flattens a list of lists into a single
 * list with all of the elements in the order they appeared in the original 
 * lists.
 *
 * flatten [[1;2;3]; []; [0]; [4;5]] = [1;2;3;0;4;5] 
 *
 * In the last assignment you wrote this function with recursion. Now, 
 * do it without explicit recursion.
 *)

let flatten (xss:'a list list) : 'a list =
  let combine_two_lists (first:'a list ) (second:'a list ) =
    foldl (fun acc ele -> ele::acc) first second in
  List.rev (foldl (fun acc lst -> combine_two_lists acc lst) [] xss);;


let _ = print_int_list (flatten [[1;2;2;];[3;4;2;];[2;4;4]]);;
