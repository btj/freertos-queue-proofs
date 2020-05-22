#use "topfind"
#require "qcheck"
open List

let rec drop k = function
  | [] -> []
  | x::xs -> if k = 0 then x::xs else drop (k-1) xs

let rec take k = function
  | [] -> []
  | x::xs -> if k = 0 then [] else x :: (take (k-1) xs)

(* cycle elements to the left *)
let rotate n xs = (drop n xs) @ (take n xs)

let rec update n v = function
  | [] -> []
  | x::xs -> if n = 0 then v::xs else x :: (update (n-1) v xs)

let test_enq = QCheck.Test.make ~count:1000 ~name:"enq"
  (QCheck.quad (QCheck.list QCheck.small_nat) QCheck.small_nat QCheck.small_nat QCheck.small_nat)
  (fun (xs, k, i, z) ->
    let n = length xs in
    QCheck.assume (0 <= k && k < n); QCheck.assume (0 <= i && i < n); 
    let ys = take k (rotate i xs) in 
    take (k+1) (rotate i (update ((i+k) mod n) z xs)) = ys @ [z]);;

QCheck.Test.check_exn test_enq

let test_enq_front = QCheck.Test.make ~count:1000 ~name:"enq_front"
  (QCheck.quad (QCheck.list QCheck.small_nat) QCheck.small_nat QCheck.small_nat QCheck.small_nat)
  (fun (xs, k, i, z) ->
    let n = length xs in
    QCheck.assume (0 <= k && k < n); QCheck.assume (0 <= i && i < n);
    let ys = take k (rotate ((i+1) mod n) xs) in
    take (k+1) (rotate i (update i z xs)) = z :: ys);;

let test_deq = QCheck.Test.make ~count:1000 ~name:"deq"
  (QCheck.triple (QCheck.list QCheck.small_nat) QCheck.small_nat QCheck.small_nat)
  (fun (xs, k, i) ->
    let n = length xs in
    QCheck.assume (0 < k && k <= n); QCheck.assume (0 <= i && i < n); 
    let ys = take k (rotate i xs) in 
    take (k-1) (rotate ((i+1) mod n) xs) = tl ys);;

QCheck.Test.check_exn test_deq

(* new def of rotate *)
let rec rotate' n xs =
  match n, xs with
  | _, [] -> []
  | 0, _ -> xs
  | n, h::t -> rotate' (n-1) (t @ [h])

let test_rotate = QCheck.Test.make ~count:1000 ~name:"rotate"
  (QCheck.pair (QCheck.list QCheck.small_nat) QCheck.small_nat)
  (fun (xs, n) -> QCheck.assume (0 < length xs); rotate (n mod length xs) xs = rotate' n xs);;

QCheck.Test.check_exn test_rotate

let test_enq' = QCheck.Test.make ~count:1000 ~name:"enq'"
  (QCheck.quad (QCheck.list QCheck.small_nat) QCheck.small_nat QCheck.small_nat QCheck.small_nat)
  (fun (xs, k, i, z) ->
    let n = length xs in
    QCheck.assume (0 <= k && k < n);
    let ys = take k (rotate' i xs) in 
    take (k+1) (rotate' i (update ((i+k) mod n) z xs)) = ys @ [z]);;

QCheck.Test.check_exn test_enq'

let test_deq' = QCheck.Test.make ~count:1000 ~name:"deq'"
  (QCheck.triple (QCheck.list QCheck.small_nat) QCheck.small_nat QCheck.small_nat)
  (fun (xs, k, i) ->
    let n = length xs in
    QCheck.assume (0 < k && k <= n);
    let ys = take k (rotate' i xs) in 
    take (k-1) (rotate' (i+1) xs) = tl ys);;

QCheck.Test.check_exn test_deq'
