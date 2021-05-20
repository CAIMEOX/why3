open Why3

open Ident
open Term
open Decl
open Task

open Cert_certificates

let thunk t _ = t

let decl_cert f = Trans.decl_acc idc (++) (fun d _ -> f d)
let decl_l_cert f = Trans.decl_l_acc idc (++) (fun d _ -> f d)

(* Identity transformation with a certificate *)
let id_ctrans = Trans.store (fun task -> [task], idc)

(** Combinators on transformations with a certificate *)

(* Generalize ctrans on <task list * scert>, correspond to one parameter
   of the certificate *)
let ctrans_gen (ctr : ctrans) (ts, c : task list * scert) =
  let llt, lc = List.split (List.map (Trans.apply ctr) ts) in
  List.flatten llt, c +++ lc

(* Apply a <ctrans> and then apply another <ctrans> on every <task> generated by
   the first one *)
let compose (tr1 : ctrans) (tr2 : ctrans) : ctrans =
  Trans.store (fun t -> Trans.apply tr1 t |> ctrans_gen tr2)

let compose_list l = List.fold_left compose id_ctrans l

(* If Then Else on transformations with a certificate : applies [tri], if the
   task changed then apply [trt] else apply [tre] *)
let ite tri trt tre = Trans.store (fun task ->
  let (lt, _) as tri_task = Trans.apply tri task in
  if not (Lists.equal task_equal lt [task])
  then ctrans_gen trt tri_task
  else ctrans_gen tre tri_task)

(* Try on transformations with a certificate : try each transformation in <lctr>
   and keep the one that closes the <task> *)
let rec try_close (lctr : ctrans list) : ctrans = Trans.store (fun task ->
  match lctr with
  | [] -> Trans.apply id_ctrans task
  | h::t -> let lctask_h, cert_h = Trans.apply h task in
            if lctask_h = []
            then [], cert_h
            else Trans.apply (try_close t) task)

(* Repeat on a transformation with a certificate : keep applying <ctr> as long
   as the tasks change *)
let repeat (ctr : ctrans) : ctrans = Trans.store (fun task ->
  let gen_task = Trans.apply id_ctrans task in
  let gen_tr = ctrans_gen ctr in
  let rec loop gt =
    let new_gt = gen_tr gt in
    if Lists.equal task_equal (fst new_gt) (fst gt)
    then gt
    else loop new_gt in
  loop gen_task)

(** Primitive transformations with a certificate *)

(* First, some utility functions *)
let default_goal task = function
  | Some pr -> pr
  | None -> task_goal task

type target =
  | Pr of prsymbol
  | Everywhere
  | Anywhere
  | Nowhere

let find_target any every where task =
  if any then Anywhere
  else if every then Everywhere
  else Pr (default_goal task where)

let match_tg tg pr = match tg with
  | Pr pr' -> pr_equal pr' pr
  | Everywhere | Anywhere -> true
  | Nowhere -> false

let update_tg_c (tg, c1) co =
  match tg, co with
  | Everywhere, Some c2 -> Everywhere, c1 ++ c2
  | Everywhere, None -> Everywhere, c1
  | _, Some c2 -> Nowhere, c2
  | _, None -> tg, c1

let revert_cert pr decls =
  let rec rc = function
    | [] -> idc
    | h::tail ->
        match h.d_node with
        | Dprop (_, pr_d, _) ->
            swap pr_d ++
              construct pr_d pr pr ++
                fold pr ++
                  rc tail
        | Dparam ls ->
            let pr' = pr_clone pr in
            llet pr (fun g ->
                let tx = t_app_infer ls [] in
                let ix' = id_fresh ls.ls_name.id_string in
                let x' = create_vsymbol ix' (Opt.get ls.ls_value) in
                let closed_t map =
                  let g = t_replace tx (t_var x') (Mid.find g map) in
                  t_forall_close [x'] [] g in
                assertion pr' closed_t +++
                  [clear pr ++ forget ls ++ rename pr' pr ++ (rc tail);
                   instquant pr' pr' tx ++ axiom pr' pr])
        | _ -> assert false in
  rc decls

let intro_cert pr decls =
  let rec ic decls = match decls with
    |  [] -> idc
    |  {d_node = Dparam _}::_ ->
         let rec intro_decls_var acc = function
           | {d_node = Dparam ls} :: l -> intro_decls_var (ls::acc) l
           | l -> List.rev acc, l in
         let lls, decls = intro_decls_var [] decls in
         List.fold_right (fun ls c -> introquant pr ls ++ c)
           lls (ic decls)
    | {d_node = Dprop (_, npr, _)}::decls ->
        unfold pr ++
          destruct pr npr pr ++
            swap npr ++ ic decls
    | _ -> assert false in
  ic (List.rev decls)
