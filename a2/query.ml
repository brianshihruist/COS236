(* Box office analysis *)

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
let print_movie (title, studio, gross, year) = 
  print_string "("; 
  print_string title; 
  print_string ", ";
  print_string studio; 
  print_string ", ";
  print_float gross; 
  print_string ", ";
  print_int year;
  print_string ")";
  print_string "\n";;

let print_movie_list = print_list print_movie;;

(* Contents:
    -- the movie type
    -- the studio_gross type
    -- functions for querying and transforming lists of movies
*)

(* a movie is a tuple of (title, studio, gross in millions, year) *)
type movie = string * string * float * int

(* a studio_gross is a pair of (studio, gross in millions) *)
type studio_gross = string * float

(* call bad_argument if your function receives a bad argument *)
(* do not change this exception or function                   *)
exception Bad_arg of string
let bad_arg (s:string) = raise (Bad_arg s)

(* a useful debugging routine *)
let debug s = print_string s; flush_all()

(* *** DO NOT CHANGE DEFINITIONS ABOVE THIS LINE! *** *)

(* you may add "rec" after any of the let declarations below that you
 * wish if you find doing so useful. *)


(* find the average gross of the movies in the list                  *)
(* return 0.0 if the list is empty                                   *)
(* hint: you may need to use functions float_of_int and int_of_float *)
(* hint: if you don't know what those functions do,                  *)
(*       type them in to ocaml toplevel                              *)
(* hint: recall the difference between +. and + also 0. and 0        *)
let average (movies : movie list) : float = 
  let rec count (movies : movie list) = 
    match movies with
    | [] -> 0
    | hd::tail -> 1 + count tail 
    in
  let rec sum (movies: movie list) =
    match movies with
    | [] -> 0.0
    | (title, studio, gross, year)::tl -> gross +. sum tl
  in
  sum movies /. float_of_int(count movies);;



(* return a list containing only the movies from the given decade *)
(* call bad_arg if n is not 20, 30, ..., 90, 00, 10               *)
(* Treat 0 as 00 (this is unavoidable as 00 is not represented    *)
(*   differently from 0).                                         *)
(* Note: movies from any years outside the range 1920-2019 will   *)
(* always be discarded but should not raise an error condition    *)
let decade (n:int) (ms:movie list) : movie list =  
  failwith "decade unimplemented"


(* return the first n items from the list *)
(* if there are fewer than n items, return all of them *)
(* call bad_arg if n is negative *)
let rec take (n:int) (l:'a list)  : 'a list =
  if n < 0 
    then bad_arg "error"
  else 
    if n = 0
      then []
    else
      match l with
      | [] -> []
      | hd::tail -> hd::take (n-1) tail;;


(* return everything but the first n items from the list *)
(* if there are fewer than n items, return the empty list *)
(* call bad_arg if n is negative *)
let rec drop (n:int) (l:'a list)  : 'a list =
    if n = 0
      then l
      else match l with
      [] -> []
      | hd::tail -> drop (n-1) tail;;


(* return a list [x1; x2; ...; xn] with the same elements as the input l
   and where:
     leq xn xn-1
     ...
     leq x3 x2
     leq x2 x1
     are all true
*)
(* hint: define an auxiliary function "select" *)

type 'a less = 'a -> 'a -> bool
let rec selection_sort (leq:'a less) (l:'a list) : 'a list =
  let rec select small lst =
  match lst with
  | [] -> (small, [])
  | h::t ->
    let (s, la) = if leq h small then (h, small) else (small, h) in
    let (smallest, rm) = select s t in
    (smallest, la::rm) in
  match l with
  | [] -> []
  | h::t -> match select h t with
            | (smallest, remaining) -> smallest::selection_sort leq remaining;;
 
let rec selection_sort_2 = function
    [] -> []
  | first::lst ->
      let rec select_r small output = function
          [] -> small :: selection_sort_2 output
        | x::xs when x < small -> select_r x (small::output) xs
        | x::xs                -> select_r small (x::output) xs
      in
      select_r first [] lst;;

(* ASIDE:  Why does this assignment ask you to implement selection sort?
   Insertion sort is almost always preferable to selection sort,
   if you have to implement a quadratic-time sorting algorithm.
   Insertion sort is faster, it's simpler to implement, and it's
   easier to reason about.  For smallish inputs (less than 5 or 8),
   insertion sort is typically faster than quicksort or any
   other NlogN sorting algorithm.  So, why do we ask you to implement
   selection sort?  Answer: we already showed you insertion sort
   in the lecture notes.

   ASIDE 2: But at least selection sort is better than bubble sort.
   Even Barack Obama knows that. https://www.youtube.com/watch?v=k4RRi_ntQc8
*)

(* return list of movies sorted by gross (largest gross first) *)
let sort_by_gross (movies : movie list) : movie list = 
  let less (t1, s1, g1, y1) (t2, s2, g2, y2) = if g1 < g2 then true else false in
  selection_sort less movies;;


(* return list of movies sorted by year produced (largest year first) *)
let sort_by_year (movies : movie list) : movie list = 
  failwith "sort_by_year unimplemented"


(* sort list of (studio, gross in millions) by gross in millions 
 * with the largest gross first *)
let sort_by_studio (studio_grosses : studio_gross list) : studio_gross list = 
  failwith "sort_by_studio unimplemented"


(* given list of movies,
 * return list of pairs (studio_name, total gross revenue for that studio)  *)
let by_studio (movies:movie list) : studio_gross list =
  failwith "by_studio unimplemented"


(***********)
(* Testing *)
(***********)

(* Augment the testing infrastructure below as you see fit *)

(* Test Data *)

let data1 : movie list = [
  ("The Lord of the Rings: The Return of the King","NL",377.85,2003)
]

let data2 : movie list = [
  ("The Lord of the Rings: The Return of the King","NL",377.85,2003);
  ("The Hunger Games","LGF",374.32,2012)
]

let data3 : movie list = [
  ("Harry Potter and the Sorcerer's Stone","WB",317.57555,2001);
  ("Star Wars: Episode II - Attack of the Clones","Fox",310.67674,2002);
  ("Return of the Jedi", "Fox", 309.306177, 1983)
]

let data4 : movie list = [
  ("The Lord of the Rings: The Return of the King","NL",377.85,2003);
  ("The Hunger Games","LGF",374.32,2012);
  ("The Dark Knight","WB",533.34,2008);
  ("Harry Potter and the Deathly Hallows Part 2","WB",381.01,2011)
]

let data5 : movie list = [
 ("The Dark Knight","WB",533.34,2008);
 ("Harry Potter and the Deathly Hallows Part 2","WB",381.01,2011)
]

let data6 : movie list = [
  ("The Hunger Games","LGF",374.32,2012);
  ("The Lord of the Rings: The Return of the King","NL",377.85,2003);
  ("Harry Potter and the Deathly Hallows Part 2","WB",381.01,2011);
  ("The Dark Knight","WB",533.34,2008);
]

(* Assertion Testing *)

(* Uncomment the following when you are ready to test your take routine *)

(* let _ = print_movie ("The Lord of the Rings: The Return of the King","NL",377.85,2003);;

let _ = print_movie_list (take 0 data4);; *)

(* Test take *)
let _ = assert(take 0 data4 = [])
let _ = assert(take 1 data1 = data1)
let _ = assert(take 2 data4 = data2)
let _ = assert(take 5 data2 = data2)
let _ = assert(take 2 data2 = data2)

(* Test drop *)
let _ = assert (drop 2 data4 = data5)
let _ = assert ( drop 10 data4 = [])

(* Test average *)
let _ = assert(average data4 = 416.63)

(* Test Sort *)
let _ = assert(sort_by_gross data4 = data6)

(* Additional Testing Infrastructure *)

let stests : (unit -> movie list) list = [
  (fun () -> sort_by_gross data1);
  (fun () -> sort_by_gross data2);
  (fun () -> sort_by_gross data3);
  (fun () -> sort_by_gross data4)
]

let check (i:int) (tests:(unit -> 'a) list) : 'a =
  if i < List.length tests && i >= 0 then
    List.nth tests i ()
  else
    failwith ("bad test" ^ string_of_int i)
