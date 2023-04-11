open Decl
open Term
open Ident
open Trans
open Wstdlib

let def_axiom_attr = create_attribute "def_axiom"
let spec_axiom_attr = create_attribute "spec_axiom"

let decl_acc  (fn : decl -> 'a -> decl list ) (st : 'a)  (acc : Task.task) : Task.task trans =
  fold (fun task acc ->
    match task.task_decl.td_node with
    | Decl d -> List.fold_left Task.add_decl acc (fn d st)
    | _ -> Task.add_tdecl acc task.task_decl
  ) acc


let is_def lsym =
  Ident.Sattr.mem  def_axiom_attr lsym.pr_name.id_attrs ||
  String.ends_with ~suffix:"'def" lsym.pr_name.id_string

let is_spec lsym =
  Ident.Sattr.mem  spec_axiom_attr lsym.pr_name.id_attrs ||
  String.ends_with ~suffix:"'spec" lsym.pr_name.id_string

let base_name id =
  List.nth (String.split_on_char '\'' id.id_string) 0


let add_trigger lsym (term : term) : term  =
  match term.t_node with
  | Tquant (q, body) ->
    let (binders, triggers, body) = t_open_quant body in
    begin match triggers with
    | [] ->
      let call = t_app_infer lsym (List.map t_var binders) in
      let body = t_close_quant binders [[call]] body in
      t_quant q body
    (* There are already triggers, so abort inferring more *)
    | _ -> term
    end
  | _ -> term

type state = {
  mutable base_syms : lsymbol Mstr.t;
  mutable limited_syms : lsymbol Mstr.t;
}
let empty_state = { base_syms = Mstr.empty; limited_syms = Mstr.empty}

let add_sym (st : state) (lsym : lsymbol) : unit =
  st.base_syms <- Mstr.add (base_name lsym.ls_name) lsym (st.base_syms)

let add_lim (st : state) (lsym : lsymbol) : unit =
  st.limited_syms <- Mstr.add (base_name lsym.ls_name) lsym (st.limited_syms)

let make_def_limited (st : state) (k, prsym, term)  : decl list =
  let base = Mstr.find (base_name prsym.pr_name) st.base_syms in
  let nm = base.ls_name.id_string ^ "'lim
  " in
  let lim = create_lsymbol (Ident.id_derive nm (base.ls_name)) base.ls_args base.ls_value in

  let term = t_s_map (fun ty -> ty) (fun lsym -> if ls_equal base lsym
  then lim else lsym) term in
  let lim_sym = create_param_decl lim in


  let (binders, _, _) = match term.t_node with
    | Tquant (_, body) -> t_open_quant body
    | _ -> assert false  in

  let lim_spec = t_close_quant binders [[t_app_infer base (List.map t_var binders)]]
  (t_equ
  (t_app_infer lim (List.map t_var binders))
  (t_app_infer base (List.map t_var binders)))

  in

  let term = add_trigger base term in

  add_lim st lim;

  let pr = create_prsymbol (Ident.id_derive (nm^"'spec") prsym.pr_name) in

  [lim_sym; create_prop_decl Paxiom pr (t_quant Tforall lim_spec); create_prop_decl k prsym term]

let add_trigger_to_spec (st : state) (k, prsym, term) : decl =
  let base = base_name prsym.pr_name in
  let base_sym = Mstr.find base st.base_syms in
  let trigger_sym = Mstr.find_opt (base_name prsym.pr_name) st.limited_syms in
  let trigger_sym = match trigger_sym with | Some t -> t | None -> Mstr.find (base_name prsym.pr_name) st.base_syms in

  let term = t_s_map (fun ty -> ty) (fun lsym -> if ls_equal base_sym lsym
  then trigger_sym else lsym) term in

  let term = add_trigger trigger_sym term in

  create_prop_decl k prsym term

let add_triggers decl st : decl list =
Format.eprintf "%a \n" (Pretty.print_decl) decl;
Format.pp_print_flush Format.err_formatter ();

match decl.d_node with
| Dparam l -> add_sym st l; [decl]
| Dlogic ls -> List.iter (fun (l, _) ->
  Format.printf "\"%a\"\n" Pretty.print_ls l;
  Format.print_flush ();
  add_sym st l) ls; [decl]
| Dprop (k, prsym, term) when  is_def prsym ->
  make_def_limited st (k, prsym, term)
| Dprop (k, prsym, term) when  is_spec prsym ->
  [add_trigger_to_spec st (k, prsym, term)]
| d -> [decl]

let () = Trans.register_transform "add_triggers" (decl_acc add_triggers (empty_state) None)
  ~desc:""