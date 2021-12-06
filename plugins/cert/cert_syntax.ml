open Why3
open Term
open Ident
open Decl
open Task
open Ty
open Format

(** Utility **)

let print_list pre = pp_print_list ~pp_sep:pp_print_space pre

exception Certif_verification_failed of string
let verif_failed s = raise (Certif_verification_failed s)

(** To certify transformations, we will represent Why3 tasks by ctask, its terms
   by cterm and type those terms with ctype *)

type cquant = CTforall | CTexists | CTlambda

type ctype =
  | CTyvar of tvsymbol (* type variable *)
  | CTprop (* type of formulas *)
  | CTyapp of tysymbol * ctype list (* (possibly) applied type symbol *)
  | CTarrow of ctype * ctype (* arrow type *)

(* Interpreted types *)
let ctint = CTyapp (ts_int, [])
let ctreal = CTyapp (ts_real, [])
let ctbool = CTyapp (ts_bool, [])

(** Utility functions on ctype *)

(* Syntactic equality *)
let rec cty_equal ty1 ty2 = match ty1, ty2 with
  | CTprop, CTprop -> true
  | CTyvar v1, CTyvar v2 -> Ty.tv_equal v1 v2
  | CTyapp (ty1, l1), CTyapp (ty2, l2) ->
      ts_equal ty1 ty2 && List.for_all2 cty_equal l1 l2
  | CTarrow (f1, a1), CTarrow (f2, a2) ->
      cty_equal f1 f2 && cty_equal a1 a2
  | (CTyvar _ | CTyapp _ | CTarrow _ | CTprop), _ -> false

let rec find_vars = function
  | CTyvar tv -> Stv.singleton tv
  | CTprop -> Stv.empty
  | CTyapp (_, l) ->
      List.fold_left (fun s ty -> Stv.union s (find_vars ty))
        Stv.empty l
  | CTarrow (ty1, ty2) ->
      Stv.union (find_vars ty1) (find_vars ty2)

(* Beware variable capture when substituting types *)
let rec cty_ty_subst subst = function
  | CTyvar tv' when Mtv.mem tv' subst -> Mtv.find tv' subst
  | CTarrow (cty1, cty2) ->
      CTarrow (cty_ty_subst subst cty1, cty_ty_subst subst cty2)
  | CTyapp (ts, l) ->
      CTyapp (ts, List.map (cty_ty_subst subst) l)
  | (CTyvar _ | CTprop) as cty -> cty

let comparing_substs l1 l2 =
  let new_ctyvar _ = CTyvar (create_tvsymbol (id_fresh "dummy_comparing_substs")) in
  let lty = List.map new_ctyvar l1 in
  let subst1 = Mtv.of_list (List.combine l1 lty) in
  let subst2 = Mtv.of_list (List.combine l2 lty) in
  subst1, subst2

(* Equality of types modulo α-conversion (only used for task equality) *)
let cty_same ty1 ty2 =
  try
    let ltv1 = Stv.elements (find_vars ty1) in
    let ltv2 = Stv.elements (find_vars ty2) in
    let subst1, subst2 = comparing_substs ltv1 ltv2 in
    let ty1 = cty_ty_subst subst1 ty1 in
    let ty2 = cty_ty_subst subst2 ty2 in
    cty_equal ty1 ty2
  with _ -> false

let rec is_predicate = function
  | CTprop -> true
  | CTarrow (_, ct) -> is_predicate ct
  | _ -> false

(* We define two printers, <hip> for premises, <ip> for everything else. This is
   needed because the logical definitions (via Dlogic) uses the same ident for
   the defined symbol and for its axiom's name. *)
let san =
  let lower_h c = if c = 'H' then "h" else char_to_alnum c in
  sanitizer lower_h char_to_alnum

let hsan s = "H" ^ san s

let ip = create_ident_printer ~sanitizer:san []
let hip = create_ident_printer ~sanitizer:hsan []

let prid fmt i = fprintf fmt "%s" (id_unique ip i)

let prhyp fmt i = fprintf fmt "%s" (id_unique hip i)

let prls fmt ls = prid fmt ls.ls_name

let prpr fmt pr = prhyp fmt pr.pr_name

let rec collect acc = function
  | CTyapp (_, l) -> List.fold_left collect acc l
  | CTarrow (t1, t2) -> collect (collect acc t1) t2
  | CTprop -> acc
  | CTyvar v -> Stv.add v acc

(** Pretty printing of ctype (compatible with lambdapi) *)
(* Prints a shallow type without outside parentheses *)
let rec prty fmt ty =
  let ltv = Stv.elements (collect Stv.empty ty) in
  pp_print_list ~pp_sep:pp_print_space
    (fun fmt tv -> fprintf fmt "Π %a : Type,@ " Pretty.print_tv tv) fmt ltv;
  prty_comp fmt ty

and prty_comp fmt = function
  | CTyapp (ts, l) when l <> [] ->
      fprintf fmt "@[<2>%a@ %a@]"
        prts ts
        (print_list prty_paren) l
  | CTarrow (t1, t2) ->
      fprintf fmt "@[%a →@ %a@]"
        prty_paren t1
        prty_comp t2
  | ty -> prty_paren fmt ty

(* Prints a shallow type, protected with outside parentheses if needed *)
and prty_paren fmt = function
  | CTyvar v -> fprintf fmt "εₜ %a" Pretty.print_tv v
  | CTprop -> fprintf fmt "Type"
  | CTyapp (ts, []) -> prts fmt ts
  | cty -> fprintf fmt "(%a)" prty_comp cty

and prts fmt ts =
  if ts_equal ts ts_int then fprintf fmt "Z"
  else if ts_equal ts ts_bool then fprintf fmt "boolean"
  else fprintf fmt "εₜ %a" Pretty.print_ts ts

(* pred functions know if we are printing the type of a predicate or not *)
(* Prints a deep type, protected with outside parentheses if needed *)
(* TODO: print quantification on type variables *)
let rec pred_ty pred fmt ty = match ty with
  | CTyapp (ts, l) when l <> [] ->
      fprintf fmt "@[<2>%a@ %a@]"
        Pretty.print_ts ts
        (print_list (pred_pty pred)) l
  | CTarrow (t1, t2) ->
      fprintf fmt "@[%a %a@ %a@]"
        (pred_pty pred) t1
        prarrow pred
        (pred_ty pred) t2
  | _ -> pred_pty pred fmt ty
and pred_pty pred fmt = function
  | CTyvar v -> Pretty.print_tv fmt v
  | CTprop -> fprintf fmt "DType"
  | CTyapp (ts, []) -> Pretty.print_ts fmt ts
  | cty -> fprintf fmt "(%a)" (pred_ty pred) cty

and prarrow fmt pred =
  if pred then fprintf fmt "⇁"
  else fprintf fmt "⇒"

(* Prints a deep type without outside parentheses *)
let prdty fmt ty =
  pred_ty (is_predicate ty) fmt ty
(* Prints a deep type, protected with outside parentheses if needed *)
let prdty_paren fmt ty =
  pred_pty (is_predicate ty) fmt ty

type cterm =
  | CTqtype of tvsymbol list * cterm (* type quantifier binding, assumed to only
                                        be in prenex form, written Π *)
  | CTbvar of int (* bound variables use De Bruijn indices *)
  | CTfvar of ident * ctype list (* free variables use a name and a list of
                                    types it is applied to *)
  | CTint of BigInt.t
  | CTapp of cterm * cterm (* binary application *)
  | CTbinop of binop * cterm * cterm (* application of a binary operator,
                                        written ∧, ∨, ⇒ and ⇔ *)
  | CTquant of cquant * ctype * cterm (* quantifier bindings: ∃, ∀ and λ *)
  | CTnot of cterm (* négation: ¬ *)
  | CTtrue (* true formula: ⊤ *)
  | CTfalse (* false formula: ⊥ *)

(* Interpreted terms *)
let id_eq = ps_equ.ls_name
let id_true = fs_bool_true.ls_name
let id_false = fs_bool_false.ls_name
let le_str = op_infix "<="
let ge_str = op_infix ">="
let lt_str = op_infix "<"
let gt_str = op_infix ">"
let pl_str = op_infix "+"
let ml_str = op_infix "*"
let pre_mn_str = op_infix "-"
let inf_mn_str = op_prefix "-"

let eq cty = CTfvar (id_eq, [cty])

(** Utility functions on cterm *)

let ct_map f ct = match ct with
  | CTbvar _ | CTfvar _ | CTint _ | CTtrue | CTfalse -> ct
  | CTquant (q, cty, ct) -> CTquant (q, cty, f ct)
  | CTqtype (i, ct) -> CTqtype (i, f ct)
  | CTapp (ct1, ct2) -> CTapp (f ct1, f ct2)
  | CTbinop (op, ct1, ct2) ->  CTbinop (op, f ct1, f ct2)
  | CTnot ct -> CTnot (f ct)

(* Warning: beware variable capture *)
let rec ct_ty_subst subst = function
  | CTquant (q, qcty, ct) ->
      CTquant (q, cty_ty_subst subst qcty,
               ct_ty_subst subst ct)
  | CTfvar (i, l) -> CTfvar (i, List.map (cty_ty_subst subst) l)
  | ct -> ct_map (ct_ty_subst subst) ct

let ct_equal t1 t2 =
  let rec ct_equal subst1 subst2 t1 t2 =
    let ct_eq t1 t2 = ct_equal subst1 subst2 t1 t2 in
    match t1, t2 with
    | CTbvar lvl1, CTbvar lvl2 -> lvl1 = lvl2
    | CTfvar (i1, l1), CTfvar (i2, l2) ->
        id_equal i1 i2 && List.for_all2 cty_equal l1 l2
    | CTapp (tl1, tr1), CTapp (tl2, tr2) ->
        ct_eq tl1 tl2 && ct_eq tr1 tr2
    | CTbinop (op1, tl1, tr1), CTbinop (op2, tl2, tr2) ->
        op1 = op2 && ct_eq tl1 tl2 && ct_eq tr1 tr2
    | CTquant (q1, ty1, t1), CTquant (q2, ty2, t2) when q1 = q2 ->
        let ty1 = cty_ty_subst subst1 ty1 in
        let ty2 = cty_ty_subst subst2 ty2 in
        cty_equal ty1 ty2 && ct_eq t1 t2
    | CTtrue, CTtrue | CTfalse, CTfalse -> true
    | CTnot t1, CTnot t2 -> ct_eq t1 t2
    | CTint i1, CTint i2 -> BigInt.eq i1 i2
    | (CTbvar _ | CTfvar _ | CTapp _ | CTbinop _ | CTquant _
       | CTqtype _ | CTtrue | CTfalse | CTnot _ | CTint _), _ -> false
  in
  match t1, t2 with
      | CTqtype (l1, t1), CTqtype (l2, t2) when List.length l1 = List.length l2 ->
          let subst1, subst2 = comparing_substs l1 l2 in
          ct_equal subst1 subst2 t1 t2
      | _, _ -> ct_equal Mtv.empty Mtv.empty t1 t2

(* Bound variable substitution *)
let rec ct_bv_subst k u ctn = match ctn with
  | CTbvar i -> if i = k then u else ctn
  | CTquant (q, cty, ct) ->
      let nct = ct_bv_subst (k+1) u ct in
      CTquant (q, cty, nct)
  | _ -> ct_map (ct_bv_subst k u) ctn

let ct_open t u = ct_bv_subst 0 u t

(* Checks if the term is locally closed *)
let locally_closed =
  let di = id_register (id_fresh "dummy_locally_closed_ident") in
  let dv = CTfvar (di, []) in
  let rec term ct = match ct with
    | CTbvar _ -> false
    | CTapp (ct1, ct2)
    | CTbinop (_, ct1, ct2) -> term ct1 && term ct2
    | CTquant (_, _, t) -> term (ct_open t dv)
    | CTqtype (_, ct)
    | CTnot ct -> term ct
    | CTint _ | CTfvar _ | CTtrue | CTfalse -> true
  in
  term

(* Free variable substitution (u should be locally closed) *)
let rec ct_fv_subst z u ctn = match ctn with
  | CTfvar (x, _) -> if id_equal z x then u else ctn
  | _ -> ct_map (ct_fv_subst z u) ctn

let ct_subst (m : cterm Mid.t) ct =
  Mid.fold ct_fv_subst m ct

(* Variable closing *)
let rec ct_fv_close x k ct = match ct with
  | CTfvar (y, l) -> if id_equal x y then (assert (l = []);  CTbvar k) else ct
  | CTquant (q, cty, ct) -> CTquant (q, cty, ct_fv_close x (k+1) ct)
  | _ -> ct_map (ct_fv_close x k) ct

let ct_close x t = ct_fv_close x 0 t

let rec replace_cterm tl tr t =
  if ct_equal t tl
  then tr
  else ct_map (replace_cterm tl tr) t

(** Pretty printing of terms (compatible with lambdapi) *)

let rec pcte fmt = function
  | CTqtype (tv::l, t) ->
      fprintf fmt "`π %a : Type, %a"
        Pretty.print_tv tv
        pcte (CTqtype(l, t))
  | CTqtype ([], t) ->
      pquant fmt t
  | t -> pquant fmt t

and pquant fmt = function
  | CTquant (q, cty, t) ->
      let x = id_register (id_fresh "x") in
      let t_open = ct_open t (CTfvar (x, [])) in
      let q_str = match q with CTforall -> "`∀"
                             | CTexists -> "`∃"
                             | CTlambda -> "λ" in
      fprintf fmt "%s %a : %a, %a"
        q_str
        prid x
        prty_paren cty
        pquant t_open;
      forget_id ip x
  | ct -> prarr fmt ct

and prarr fmt = function
  | CTbinop (Timplies, ct1, ct2) ->
      fprintf fmt "%a ⇒ %a"
        prdisj ct1
        prarr ct2
  | CTbinop (Tiff, ct1, ct2) ->
      fprintf fmt "%a ⇔ %a"
        prdisj ct1
        prarr ct2
  | ct -> prdisj fmt ct

and prdisj fmt = function
  | CTbinop (Tor, ct1, ct2) ->
      fprintf fmt "%a ∨ %a"
        prconj ct1
        prdisj ct2
  | ct -> prconj fmt ct

and prconj fmt = function
  | CTbinop (Tand, ct1, ct2) ->
      fprintf fmt "%a ∧ %a"
        prnot ct1
        prconj ct2
  | ct -> prnot fmt ct

and prnot fmt = function
  | CTnot ct ->
      fprintf fmt "¬ %a"
        prpv ct
  | ct -> prapp fmt ct

and prapp fmt = function
  | CTapp (ct1, ct2) ->
      fprintf fmt "%a %a"
        prapp ct1
        prpv ct2
  | CTint i when BigInt.sign i < 0 ->
      fprintf fmt "~ %s" BigInt.(to_string (abs i))
  | ct -> prpv fmt ct

and prpv fmt = function
  | CTbvar n -> pp_print_int fmt n
  | CTfvar (id, l) ->
      begin match l with
      | [] -> prid fmt id
      | _ -> prid fmt id;
             List.iter (fprintf fmt " %a" prdty_paren) l
      end
  | CTint i when BigInt.sign i >= 0 ->
      pp_print_string fmt (BigInt.to_string i)
  | CTfalse -> fprintf fmt "⊥"
  | CTtrue -> fprintf fmt "⊤"
  | ct -> fprintf fmt "(%a)" pcte ct

type 't ctask =
  { uid : ident; (* A unique identifier of the task *)
    get_ls : string -> lsymbol; (* remember interpreted symbols for efficiency*)
    types_interp : Sid.t; (* interpreted types *)
    types : Sid.t; (* types *)
    sigma_interp : ctype Mid.t; (* interpreted variables with their type *)
    sigma : ctype Mid.t; (* variables with their type *)
    gamma_delta : ('t * bool) Mid.t (* names of premises with their formula and
    their positivity (false means it's an hypothesis, true means it's a goal) *)
  }

type kernel_ctask = cterm ctask

(** Pretty printing of ctask *)

let po p fmt = function
  | None -> fprintf fmt "None"
  | Some x -> fprintf fmt "%a" p x

let prt fmt sid =
  Sid.iter (fun i -> fprintf fmt "%a@ " prid i) sid

let prs fmt mid =
  Mid.iter (fun x ty -> fprintf fmt "%a : %a@ " prid x prty ty) mid

let prpos fmt = function
  | true  -> fprintf fmt "GOAL| "
  | false -> fprintf fmt "HYP | "

let prprop pt fmt h (t, pos) =
  fprintf fmt "%a%a : %a@ " prpos pos prhyp h pt t

let prgd pt fmt mid =
  Mid.iter (prprop pt fmt) mid


let gen_pcta pt fmt cta =
  fprintf fmt "@[<v>TYPES INTERP:@ %a@ \
               TYPES:@ %a@ \
               SIGMA INTERP:@ %a@ \
               SIGMA:@ %a@ \
               %a@]@."
    prt cta.types_interp
    prt cta.types
    prs cta.sigma_interp
    prs cta.sigma
    (prgd pt) cta.gamma_delta

let pacta = gen_pcta pcte

let pcta = gen_pcta Pretty.print_term

let plcta =
  pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "========@ ") pacta

let eplcta cta lcta =
  eprintf "@[<v>INIT :@ \
           %a==========@ \
           RES :@ \
           %a@]@."
    pacta cta
    plcta lcta

let print_ctasks filename lcta =
  let filename = Sysutil.uniquify filename in
  let oc = open_out filename in
  let fmt = formatter_of_out_channel oc in
  fprintf fmt "@[<v>RESULTING TASKS:@ @ \
               %a@]@."
    plcta lcta;
  close_out oc

(** Utility functions on ctask (used notably in caml checker) *)

let ctask_equal cta1 cta2 =
  Mid.equal cty_same cta1.sigma cta2.sigma &&
    let cterm_pos_equal (t1, p1) (t2, p2) =
      ct_equal t1 t2 && p1 = p2 in
    Mid.equal cterm_pos_equal cta1.gamma_delta cta2.gamma_delta

let find_variable s i cta =
  match Mid.find_opt i cta.sigma with
  | Some x -> x
  | None ->
      let s = asprintf "%s : Can't find a variable with name %a in the task"
                s prid i in
      verif_failed s

let find_formula s h cta =
  match Mid.find_opt h cta.gamma_delta with
  | Some x -> x
  | None ->
      let s = asprintf "%s : Can't find a formula with name %a in the task"
                s prhyp h in
      verif_failed s

let ctask_new get_ls types_interp sigma_interp =
  { uid = id_register (id_fresh "s");
    get_ls;
    types_interp;
    types = Sid.empty;
    sigma_interp;
    sigma = Mid.empty;
    gamma_delta = Mid.empty }

let dummy_ctask _ =
  ctask_new (fun _ -> assert false) Sid.empty Mid.empty

let lift_mid_cta f cta =
  { cta with gamma_delta = f (cta.gamma_delta) }

(* Make sure to not add interpreted types to the abstract types *)
let add_type i cta =
  if Sid.mem i cta.types_interp then cta
  else { cta with types = Sid.add i cta.types }

(* Make sure to not add interpreted variables to the signature *)
let add_var i cty cta =
  if Mid.mem i cta.sigma_interp then cta
  else { cta with sigma = Mid.add i cty cta.sigma  }

let remove_var i cta =
  { cta with sigma = Mid.remove i cta.sigma  }

let remove i cta = lift_mid_cta (Mid.remove i) cta

let add i ct cta = lift_mid_cta (Mid.add i ct) cta


(* Separates hypotheses and goals *)
let split_hyp_goal cta =
  let open Mid in
  fold (fun h (ct, pos) (gamma, delta) ->
      if pos then gamma, add h (ct, pos) delta
      else add h (ct, pos) gamma, delta)
    cta (empty, empty)

(* Creates a new ctask with the same hypotheses but sets the goal with the
   second argument *)
let set_goal cta =
  let gamma, delta = split_hyp_goal cta.gamma_delta in
  let gpr, _ = Mid.choose gamma in
  fun ct ->
  { cta with
    gamma_delta = Mid.add gpr (ct, true) delta }


let instantiate f a =
  match f with
  | CTquant (CTlambda, _, f) -> ct_open f a
  | _ -> assert false

(* Verify that an ident is fresh in relation to a context of propositions *)
exception Found
let has_ident_context i ctxt =
  let rec found_ident_term i t = match t with
    | CTfvar (i', _) when id_equal i i' -> raise Found
    | _ -> ct_map (found_ident_term i) t in
  try Mid.map (fun (t, _) -> found_ident_term i t)
        ctxt |> ignore; false
  with Found -> true

(* Typing algorithm *)

let rec type_matching subst ty1 ty2 = match ty1, ty2 with
  | CTprop, CTprop -> subst
  | CTyvar v, _ ->
      begin match Mtv.find_opt v subst with
      | None -> Mtv.add v ty2 subst
      | Some ty2' -> assert (cty_equal ty2 ty2'); subst end
  | CTyapp (ts1, l1), CTyapp (ts2, l2) ->
      assert (ts_equal ts1 ts2);
      for_all2_type_matching subst l1 l2
  | CTarrow (f1, a1), CTarrow (f2, a2) ->
      for_all2_type_matching subst [f1; a1] [f2; a2]
  | (CTyapp _ | CTarrow _ | CTprop), _ ->
      assert false

and for_all2_type_matching subst l1 l2 = match l1, l2 with
  | [], [] -> subst
  | h1::t1, h2::t2 ->
      let subst = type_matching subst h1 h2 in
      for_all2_type_matching subst t1 t2
  | _ -> assert false


let infer_type cta t =
  let rec infer_type sigma t = match t with
    | CTfvar (v, l) ->
        begin match Mid.find_opt v sigma with
        | Some ty ->
            let formal_l = Stv.elements (find_vars ty) in
            let subst = Mtv.of_list (List.combine formal_l l) in
            cty_ty_subst subst ty
        | None -> failwith "Can't find variable in sigma" end
    | CTbvar _ -> failwith "unbound variable"
    | CTtrue | CTfalse -> CTprop
    | CTnot t -> let ty = infer_type sigma t in
                 begin try assert (cty_equal ty CTprop);
                     CTprop
                 with _ -> failwith "not should be applied on prop only" end
    | CTquant (quant, ty1, t) ->
        assert (Mtv.is_empty (find_vars ty1));
        let ni = id_register (id_fresh "type_ident") in
        let sigma = Mid.add ni ty1 sigma in
        let t = ct_open t (CTfvar (ni, [])) in
        let ty2 = infer_type sigma t in
        begin match quant with
        | CTlambda -> CTarrow (ty1, ty2)
        | CTforall | CTexists ->
            try assert (cty_equal ty2 CTprop);
                CTprop
            with _ -> failwith "quantification on non prop" end
    | CTqtype (_, ct) -> infer_type sigma ct
    | CTapp (t1, t2) ->
        begin match infer_type sigma t1, infer_type sigma t2 with
        | CTarrow (ty1, ty2), ty3 ->
            let subst = type_matching Mtv.empty ty1 ty3 in
            cty_ty_subst subst ty2
        | _ -> failwith "can't apply non functions"
        end
    | CTbinop (_, t1, t2) ->
        let ty1, ty2 = infer_type sigma t1, infer_type sigma t2 in
        begin try assert (cty_equal ty1 CTprop);
                  assert (cty_equal ty2 CTprop);
                  CTprop
              with _ -> failwith "binop on non prop" end
    | CTint _ -> ctint in
  let sigma_plus_interp = Mid.set_union cta.sigma cta.sigma_interp in
  infer_type sigma_plus_interp t

let well_typed cta t =
  ignore (infer_type cta t)

let infers_into ?e_str:(s="") cta t ty =
  try assert (cty_equal (infer_type cta t) ty)
  with e ->
    eprintf "@[<v>Checking %s: wrong type for %a@ \
             expected: %a@]@." s pcte t prty ty;
            raise e

let instantiate_safe cta f a =
  well_typed cta f;
  let ty = infer_type cta a in
  match f with
  | CTquant (CTlambda, ty', f) when cty_equal ty ty' ->
      ct_open f a
  | _ -> assert false

(** We instrument existing transformations to produce a certificate *)

type 'certif ctransformation = (task list * 'certif) Trans.trans
