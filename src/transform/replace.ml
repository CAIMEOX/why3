open Theory
open Decl
open Term

let meta_replace =
  register_meta "trans:replace_predicate" [ MTlsymbol; MTlsymbol ]
    ~desc:"Replace@ a@ predicate@ by@ one@ with@ the@ same signature."

let rec rep_in_term args t =
  let rep = rep_in_term args in
  match t.t_node with
  | Tapp (ls, terms) ->
    let ls =
      List.fold_left
        (fun ls ls_l ->
          match ls_l with
          | [] -> ls
          | [ ls1; ls2 ] ->
            let ls1 =
              match ls1 with
              | MAls ls1 -> ls1
              | _ -> assert false
            in
            let ls2 =
              match ls2 with
              | MAls ls2 -> ls2
              | _ -> assert false
            in
            if ls_equal ls ls1 then
              ls2
            else
              ls
          | _ -> assert false)
        ls args
    in
    let terms = List.map rep terms in
    t_app_infer ls terms
  | Tif (t1, t2, t3) -> t_if (rep t1) (rep t2) (rep t3)
  | Tlet (term, term_bound) ->
    let vs, t = t_open_bound term_bound in
    let t = rep t in
    let term_bound = t_close_bound vs t in
    t_let (rep term) term_bound
  | Tcase (term, term_branchs) -> t_case (rep term) term_branchs
  | Teps term_bound -> assert false
  | Tquant (quant, term_quant) ->
    let vs, trigger, t = t_open_quant term_quant in
    let t = rep t in
    let term_quant = t_close_quant vs trigger t in
    t_quant quant term_quant
  | Tbinop (binop, t1, t2) -> t_binary binop (rep t1) (rep t2)
  | Tnot term -> t_not (rep term)
  | _ -> t

let rep args d =
  match d.d_node with
  | Dprop (kind, pr, t) ->
    let t = rep_in_term args t in
    [ create_prop_decl kind pr t ]
  | _ -> [ d ]

(* TODO : Check types *)
let replace args = Trans.decl (rep args) None
let replace_predicate = Trans.on_meta meta_replace replace

let () =
  Trans.register_transform "replace_predicate" replace_predicate
    ~desc:
      "Only@ keep@ declarations@ of@ integer@ and@ real@ variables,@ also@ \
       only@ keep@ assertions@ about@ inequalities@ or@ equalites@ between@ \
       integers@ and@ reals."