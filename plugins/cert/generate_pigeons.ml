open List
open Format
type var = int * int

type lit = bool * var
type clause = lit list

let rec range s e = if s = e + 1 then [] else s :: range (s+1) e
let iterate n v =
  let rec it i = if i = 0 then [] else v :: it (i-1) in
  it n

let pigeons n =
  let l = ref [] in
  let add cl = l := cl :: !l in
  for i = 1 to n+1 do
    add (combine (iterate n true) (combine (iterate n i) (range 1 n)))
  done;
  for j = 1 to n do
    for i1 = 1 to n do
      for i2 = i1 + 1 to n + 1 do
        add [false, (i1, j); false, (i2, j)]
      done
    done
  done;
  rev !l

let print_bool fmt b =
  if not b then fprintf fmt "not "

let print_pb fmt n =
  for i = 1 to n+1 do
    for j = 1 to n do
      fprintf fmt "val constant p_%d_%d : bool@ " i j
    done
  done;
  fprintf fmt "@ goal pigeons : not (@ %a@ )"
    (pp_print_list
       ~pp_sep:(fun fmt _ -> fprintf fmt " /\\@ ")
       (fun fmt cl ->
         fprintf fmt "(%a)"
           (pp_print_list
              ~pp_sep:(fun fmt _ -> fprintf fmt " \\/ ")
              (fun fmt (b, (i, j)) ->
                fprintf fmt "%ap_%d_%d" print_bool b i j))
           cl
       )
    )

    (pigeons n)


let _ =
  let n = Sys.argv.(1) |> int_of_string in
  let fn = sprintf "pigeon%d.mlw" n in
  let out = open_out fn in
  let fmt = formatter_of_out_channel out in
  fprintf fmt "@[<v>%a@]@."
    print_pb n
