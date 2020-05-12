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
