type t = (Z.t) list

let empty (_: unit) : t = [] 

let rec add_list (x: Z.t) (ys: (Z.t) list) : (Z.t) list =
  match ys with
  | [] -> x :: [] 
  | y :: ys' ->
    if Z.lt x y
    then x :: ys
    else begin if Z.equal x y then ys else y :: add_list x ys' end

let add (x: Z.t) (s: t) : t = add_list x s

let rec mem_list (x: Z.t) (ys: (Z.t) list) : bool =
  match ys with
  | [] -> false
  | y :: ys1 -> if Z.lt x y then false else Z.equal x y || mem_list x ys1

let mem (x: Z.t) (s: t) : bool = mem_list x s

let main (_: unit) : (bool) * (bool) =
  let s = empty () in
  let s1 = add Z.one s in
  let s2 = add (Z.of_string "2") s1 in
  let s3 = add (Z.of_string "3") s2 in
  let b1 = mem (Z.of_string "3") s3 in
  let b2 = mem (Z.of_string "4") s3 in
  (b1, b2)

