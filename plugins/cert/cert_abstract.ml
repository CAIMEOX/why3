open Why3
open Term
open Ident
open Theory
open Decl
open Task
open Ty

(** To certify transformations, we will represent Why3 tasks by the type <ctask>
    and we equip transformations with a certificate <certif> *)

type cquant = CTforall | CTexists | CTlambda

type ctype =
  | CTyvar of tvsymbol
  | CTyapp of tysymbol * ctype list
  | CTarrow of ctype * ctype

type cterm =
  | CTbvar of int (* bound variables use De Bruijn indices *)
  | CTfvar of ident (* free variables use a name *)
  | CTint of BigInt.t
  | CTapp of cterm * cterm (* binary application *)
  | CTbinop of binop * cterm * cterm (* application of a binary operator *)
  | CTquant of cquant * ctype * cterm (* quantifier binding *)
  | CTnot of cterm
  | CTtrue
  | CTfalse

let ctbool = CTyapp (Ty.ts_bool, [])
let ctint = CTyapp (Ty.ts_int, [])



type ctask =
  { sigma : ctype Mid.t;
    gamma_delta : (cterm * bool) Mid.t
  }
(* We will denote a ctask <sigma; gamma_delta> by <Σ | Γ ⊢ Δ> where :
   • <Σ> contains all the signature declarations <x : ty> where <x> is mapped to <ty> in <sigma>
   • <Γ> contains all the declarations <H : P> where <H> is mapped to <(P, false)> in <gamma_delta>
   • <Δ> contains all the declarations <H : P> where <H> is mapped to <(P,  true)> in <gamma_delta>
*)

let ctask_empty =
  { sigma = Mid.empty;
    gamma_delta = Mid.empty }

let ctask_union ct1 ct2 =
  { sigma = Mid.set_union ct1.sigma ct2.sigma;
    gamma_delta = Mid.set_union ct1.gamma_delta ct2.gamma_delta }

let lift_mid_cta f cta =
  { sigma = cta.sigma;
    gamma_delta = f (cta.gamma_delta) }

let add_var i cty cta =
  { sigma = Mid.add i cty cta.sigma;
    gamma_delta = cta.gamma_delta }

let remove i cta = lift_mid_cta (Mid.remove i) cta

let add i ct cta = lift_mid_cta (Mid.add i ct) cta

(** Abstracting a Why3 <task> into a <ctask> : extract only the logical core *)

let abstract_quant = function
  | Tforall -> CTforall
  | Texists -> CTexists

let rec abstract_otype = function
  | None -> ctbool
  | Some ty -> abstract_type ty

and abstract_type { ty_node } =
  match ty_node with
  | Tyvar v -> CTyvar v
  | Tyapp (ts, lts) ->
      if ts_equal ts ts_func
      then let l1, l2 = match lts with
             | [l1; l2] -> l1, l2
             | _ -> assert false in
           CTarrow (abstract_type l1, abstract_type l2)
      else CTyapp (ts, List.map abstract_type lts)

let type_lsymbol ls =
  List.fold_right (fun t acc -> CTarrow (abstract_type t, acc))
    ls.ls_args (abstract_otype ls.ls_value)

let rec abstract_term t =
  abstract_term_rec Mid.empty 0 t

and abstract_term_rec bv_lvl lvl t =
  abstract_term_node_rec bv_lvl lvl t.t_node

and abstract_term_node_rec bv_lvl (lvl : int) t =
  (* level <lvl> is the number of forall above in the whole term *)
  (* <bv_lvl> is mapping bound variables to their respective level *)
  let cterm_node_sig_from_id id  = match Mid.find_opt id bv_lvl with
        | None ->
            CTfvar id
        | Some lvl_id ->
            (* a variable should not be above its definition *)
            assert (lvl_id <= lvl);
            CTbvar (lvl - lvl_id) in
  match t with
  | Tvar v ->
      cterm_node_sig_from_id v.vs_name
  | Tapp (ls, lt) ->
      let ctls = cterm_node_sig_from_id ls.ls_name in
      List.fold_left (fun acc h -> CTapp (abstract_term_rec bv_lvl lvl h, acc))
        ctls lt
  | Tbinop (op, t1, t2) ->
      let ct1 = abstract_term_rec bv_lvl lvl t1 in
      let ct2 = abstract_term_rec bv_lvl lvl t2 in
      CTbinop (op, ct1, ct2)
  | Tquant (q, tq) ->
      let lvs, _, t_open = t_open_quant tq in
      let lvl_ids = List.mapi (fun i vs -> lvl + i + 1, vs.vs_name) lvs in
      let bv_lvl = List.fold_left (fun m (lvl, ids) -> Mid.add ids lvl m) bv_lvl lvl_ids in
      let lvl = lvl + List.length lvs in
      let ctn_open = abstract_term_rec bv_lvl lvl t_open in
      let q = abstract_quant q in
      let ctquant vs ct = let cty = abstract_type vs.vs_ty in
                          CTquant (q, cty, ct) in
      let ct_closed = List.fold_right ctquant lvs ctn_open in
      ct_closed
  | Tnot t -> let ct = abstract_term_rec bv_lvl lvl t in
              CTnot ct
  | Ttrue -> CTtrue
  | Tfalse -> CTfalse
  | Tconst (Constant.ConstInt i) -> CTint i.Number.il_int
  | Tconst _ ->
      let s = "" in
      (* let open Format in
       * Pretty.print_term str_formatter t;
       * let s = flush_str_formatter () in *)
      invalid_arg ("Cert_abstract.abstract_term Tconst : " ^ s)
  | Tif _ -> invalid_arg "Cert_abstract.abstract_term Tif"
  | Tlet _ -> invalid_arg "Cert_abstract.abstract_term Tlet"
  | Tcase _ -> invalid_arg "Cert_abstract.abstract_term Tcase"
  | Teps _ -> invalid_arg "Cert_abstract.abstract_term Teps"

let abstract_decl_acc acc decl =
  match decl.d_node with
  | Dprop (k, pr, t) ->
      let ct = abstract_term t in
      add pr.pr_name (ct, k = Pgoal) acc
  | Dparam ls ->
      let cty = type_lsymbol ls in
      add_var ls.ls_name cty acc
  | _ -> acc

let abstract_tdecl_acc acc td =
  match td.td_node with
  | Decl decl -> abstract_decl_acc acc decl
  | _ -> acc

let rec abstract_task_acc acc = function
  | Some {task_decl = td; task_prev = task} ->
      let new_acc = abstract_tdecl_acc acc td in
      abstract_task_acc new_acc task
  | None -> acc

let abstract_task task =
  abstract_task_acc ctask_empty task

(** We equip existing transformations with a certificate <certif> *)

type 'certif ctransformation = (task list * 'certif) Trans.trans

exception Certif_verification_failed of string
let verif_failed s = raise (Certif_verification_failed s)


(** Create a certified transformation from a transformation with a certificate *)

type 'certif debug =
  ('certif -> unit) option *
  (ctask -> ctask list -> unit) option


let checker_ctrans
      (debug : 'certif debug )
      (make_core : ctask -> ctask list -> 'certif -> 'core_certif)
      (checker : 'core_certif -> ctask -> ctask list -> unit)
      (ctr : 'certif ctransformation)
      (init_t : task) =
  let dbg_cert, dbg_cta = debug in
  let res_t, certif = Trans.apply ctr init_t in
  Opt.iter (fun eprcertif -> eprcertif certif) dbg_cert;
  let init_ct = abstract_task init_t in
  let res_ct = List.map abstract_task res_t in
  Opt.iter (fun eplcta -> eplcta init_ct res_ct) dbg_cta;
  let core_certif = make_core init_ct res_ct certif in
  checker core_certif init_ct res_ct;
  res_t
