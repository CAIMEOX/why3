(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Ident
open Ty
open Term
open Mlw_ty
open Mlw_ty.T
open Mlw_expr

(** Program types *)

type dity =
  | Dvar of dvar ref
  | Dutv of tvsymbol
  | Dapp of itysymbol * dity list * dreg list
  | Dpur of tysymbol  * dity list

and dvar =
  | Dtvs of tvsymbol
  | Dval of dity

and dreg =
  | Rreg of region * dity
  | Rvar of rvar ref

and rvar =
  | Rtvs of tvsymbol * dity
  | Rval of dreg

type dvty = dity list * dity (* A -> B -> C == ([A;B],C) *)

let create_dreg dity =
  Rvar (ref (Rtvs (create_tvsymbol (id_fresh "rho"), dity)))

let dity_of_ity ity =
  let hreg = Hreg.create 3 in
  let rec dity ity = match ity.ity_node with
    | Ityvar tv -> Dutv tv
    | Ityapp (s,tl,rl) -> Dapp (s, List.map dity tl, List.map dreg rl)
    | Itypur (s,tl)    -> Dpur (s, List.map dity tl)
  and dreg reg =
    try Hreg.find hreg reg with Not_found ->
    let r = create_dreg (dity reg.reg_ity) in
    Hreg.add hreg reg r;
    r
  in
  dity ity

let ity_of_dity ~strict dity =
  let rec ity = function
    | Dvar { contents = Dval t } -> ity t
    | Dvar _ when strict -> Loc.errorm "undefined type variable"
    | Dvar ref ->
        let tv = create_tvsymbol (id_fresh "xi") in
        ref := Dval (Dutv tv);
        ity_var tv
    | Dutv tv -> ity_var tv
    | Dapp (s,tl,rl) -> ity_app s (List.map ity tl) (List.map reg rl)
    | Dpur (s,tl)    -> ity_pur s (List.map ity tl)
  and reg = function
    | Rreg (r,_) -> r
    | Rvar { contents = Rval r } -> reg r
    | Rvar ({ contents = Rtvs (tv,t) } as ref) ->
        let r = create_region (id_clone tv.tv_name) (ity t) in
        ref := Rval (Rreg (r,t));
        r
  in
  ity dity

(** Destructive type unification *)

let rec occur_check tv = function
  | Dvar { contents = Dval d } -> occur_check tv d
  | Dapp (_,dl,_) | Dpur (_,dl) -> List.iter (occur_check tv) dl
  | Dvar { contents = Dtvs tv' } | Dutv tv' ->
      if tv_equal tv tv' then raise Exit

let rec unify d1 d2 = match d1,d2 with
  | Dvar { contents = Dval d1 }, d2
  | d1, Dvar { contents = Dval d2 } ->
      unify d1 d2
  | Dvar { contents = Dtvs tv1 },
    Dvar { contents = Dtvs tv2 } when tv_equal tv1 tv2 ->
      ()
  | Dvar ({ contents = Dtvs tv } as r), d
  | d, Dvar ({ contents = Dtvs tv } as r) ->
      occur_check tv d;
      r := Dval d
  | Dutv tv1, Dutv tv2 when tv_equal tv1 tv2 ->
      ()
  | Dapp (s1,dl1,_), Dapp (s2,dl2,_) when its_equal s1 s2 ->
      List.iter2 unify dl1 dl2
  | Dpur (s1,dl1), Dpur (s2,dl2) when ts_equal s1 s2 ->
      List.iter2 unify dl1 dl2
  | _ -> raise Exit

(** Reunify regions *)

let dtvs_queue : dvar ref Queue.t = Queue.create ()

let unify_queue : (dity * dity) Queue.t = Queue.create ()

let dity_fresh () =
  let r = ref (Dtvs (create_tvsymbol (id_fresh "a"))) in
  Queue.add r dtvs_queue;
  Dvar r

let its_app_fresh s dl =
  let htv = Htv.create 3 in
  let hreg = Hreg.create 3 in
  let rec inst ity = match ity.ity_node with
    | Ityvar v -> Htv.find htv v
    | Ityapp (s,tl,rl) -> Dapp (s, List.map inst tl, List.map fresh rl)
    | Itypur (s,tl)    -> Dpur (s, List.map inst tl)
  and fresh r =
    try Hreg.find hreg r with Not_found ->
    let reg = create_dreg (inst r.reg_ity) in
    Hreg.add hreg r reg;
    reg in
  List.iter2 (Htv.add htv) s.its_ts.ts_args dl;
  match s.its_def with
  | None -> Dapp (s, dl, List.map fresh s.its_regs)
  | Some ity -> inst ity

let rec dity_refresh = function
  | Dvar { contents = Dval dty } -> dity_refresh dty
  | Dvar { contents = Dtvs _ } as dity -> dity
  | Dapp (s,dl,_) -> its_app_fresh s (List.map dity_refresh dl)
  | Dpur (s,dl) -> Dpur (s, List.map dity_refresh dl)
  | Dutv _ as dity -> dity

let unify ?(weak=false) d1 d2 =
  unify d1 d2;
  if not weak then Queue.add (d1,d2) unify_queue

let rec reunify d1 d2 = match d1,d2 with
  | Dvar { contents = Dval d1 }, d2
  | d1, Dvar { contents = Dval d2 } -> reunify d1 d2
  | Dvar _, Dvar _ | Dutv _, Dutv _ -> ()
  | Dapp (_,dl1,rl1), Dapp (_,dl2,rl2) ->
      List.iter2 reunify dl1 dl2;
      List.iter2 unify_reg rl1 rl2
  | Dpur (_,dl1), Dpur (_,dl2) ->
      List.iter2 reunify dl1 dl2
  | _ -> assert false

and unify_reg r1 r2 = match r1,r2 with
  | Rvar { contents = Rval r1 }, r2
  | r1, Rvar { contents = Rval r2 } ->
      unify_reg r1 r2
  | Rvar { contents = Rtvs (tv1,_) },
    Rvar { contents = Rtvs (tv2,_) } when tv_equal tv1 tv2 ->
      ()
  | Rvar ({ contents = Rtvs (_,d1) } as r),
    (Rvar { contents = Rtvs (_,d2) } as d)
  | Rvar ({ contents = Rtvs (_,d1) } as r), (Rreg (_,d2) as d)
  | (Rreg (_,d1) as d), Rvar ({ contents = Rtvs (_,d2) } as r) ->
      reunify d1 d2;
      r := Rval d
  | Rreg _, Rreg _ -> ()
    (* we don't check whether the regions are the same,
       because we won't have a good location for the error.
       Let the core API raise the exception later. *)

let reunify_regions () =
  Queue.iter (fun r -> match !r with
    | Dval d -> r := Dval (dity_refresh d)
    | Dtvs _ -> ()) dtvs_queue;
  Queue.clear dtvs_queue;
  Queue.iter (fun (d1,d2) -> reunify d1 d2) unify_queue;
  Queue.clear unify_queue

(** Chainable relations *)

let rec dity_is_bool = function
  | Dvar { contents = Dval dty } -> dity_is_bool dty
  | Dpur (ts,_) -> ts_equal ts ts_bool
  | _ -> false

let dvty_is_chainable = function
  | [t1;t2],t ->
      dity_is_bool t && not (dity_is_bool t1) && not (dity_is_bool t2)
  | _ -> false

(** Pretty-printing *)

let debug_print_reg_types = Debug.register_info_flag "print_reg_types"
  ~desc:"Print@ types@ of@ regions@ (mutable@ fields)."

let print_dity fmt dity =
  let protect_on x s = if x then "(" ^^ s ^^ ")" else s in
  let print_rtvs fmt tv = Mlw_pretty.print_reg fmt
    (create_region (id_clone tv.tv_name) Mlw_ty.ity_unit) in
  let rec print_dity inn fmt = function
    | Dvar { contents = Dtvs tv }
    | Dutv tv -> Pretty.print_tv fmt tv
    | Dvar { contents = Dval dty } -> print_dity inn fmt dty
    | Dpur (s,tl) when is_ts_tuple s -> Format.fprintf fmt "(%a)"
        (Pp.print_list Pp.comma (print_dity false)) tl
    | Dpur (s,[]) -> Pretty.print_ts fmt s
    | Dpur (s,tl) -> Format.fprintf fmt (protect_on inn "%a@ %a")
        Pretty.print_ts s (Pp.print_list Pp.space (print_dity true)) tl
    | Dapp (s,[],rl) -> Format.fprintf fmt (protect_on inn "%a@ <%a>")
        Mlw_pretty.print_its s (Pp.print_list Pp.comma print_dreg) rl
    | Dapp (s,tl,rl) -> Format.fprintf fmt (protect_on inn "%a@ <%a>@ %a")
        Mlw_pretty.print_its s (Pp.print_list Pp.comma print_dreg) rl
          (Pp.print_list Pp.space (print_dity true)) tl
  and print_dreg fmt = function
    | Rreg (r,_) when Debug.test_flag debug_print_reg_types ->
        Format.fprintf fmt "@[%a:@,%a@]" Mlw_pretty.print_reg r
          Mlw_pretty.print_ity r.reg_ity
    | Rreg (r,_) -> Mlw_pretty.print_reg fmt r
    | Rvar { contents = Rtvs (tv,dity) }
      when Debug.test_flag debug_print_reg_types ->
        Format.fprintf fmt "@[%a:@,%a@]" print_rtvs tv (print_dity false) dity
    | Rvar { contents = Rtvs (tv,_) } -> print_rtvs fmt tv
    | Rvar { contents = Rval dreg } -> print_dreg fmt dreg
  in
  print_dity false fmt dity

(* Specialization of symbols *)

let specialize_scheme tvs (argl,res) =
  let htv = Htv.create 3 and hreg = Htv.create 3 in
  let rec spec_dity = function
    | Dvar { contents = Dval dity } -> spec_dity dity
    | Dvar { contents = Dtvs tv } | Dutv tv as dity -> get_tv tv dity
    | Dapp (s,dl,rl) -> Dapp (s, List.map spec_dity dl, List.map spec_reg rl)
    | Dpur (s,dl)    -> Dpur (s, List.map spec_dity dl)
  and spec_reg = function
    | Rvar { contents = Rval r } -> spec_reg r
    | Rvar { contents = Rtvs (tv,dity) } -> get_reg tv dity
    | Rreg _ as r -> r
  and get_tv tv dity = try Htv.find htv tv with Not_found ->
    let v = dity_fresh () in
    (* can't return dity, might differ in regions *)
    if Stv.mem tv tvs then unify ~weak:true v dity;
    Htv.add htv tv v;
    v
  and get_reg tv dity = try Htv.find hreg tv with Not_found ->
    let r = create_dreg (spec_dity dity) in
    Htv.add hreg tv r;
    r in
  List.map spec_dity argl, spec_dity res

let spec_ity htv hreg vars ity =
  let get_tv tv =
    assert (not (Stv.mem tv vars.vars_tv));
    try Htv.find htv tv with Not_found ->
    let v = dity_fresh () in
    Htv.add htv tv v;
    v in
  let rec dity ity = match ity.ity_node with
    | Ityvar tv -> get_tv tv
    | Ityapp (s,tl,rl) -> Dapp (s, List.map dity tl, List.map dreg rl)
    | Itypur (s,tl)    -> Dpur (s, List.map dity tl)
  and dreg reg = try Hreg.find hreg reg with Not_found ->
    let t = dity reg.reg_ity in
    let r = if reg_occurs reg vars then Rreg (reg,t) else create_dreg t in
    Hreg.add hreg reg r;
    r
  in
  dity ity

let specialize_ity ity =
  let htv = Htv.create 3 and hreg = Hreg.create 3 in
  spec_ity htv hreg ity.ity_vars ity

let specialize_pvsymbol pv = specialize_ity pv.pv_ity

let specialize_xsymbol xs = specialize_ity xs.xs_ity

let specialize_arrow vars aty =
  let htv = Htv.create 3 and hreg = Hreg.create 3 in
  let conv pv = spec_ity htv hreg vars pv.pv_ity in
  let rec specialize a =
    let argl = List.map conv a.aty_args in
    let narg,res = match a.aty_result with
      | VTvalue v -> [], spec_ity htv hreg vars v
      | VTarrow a -> specialize a
    in
    argl @ narg, res
  in
  specialize aty

let specialize_psymbol ps =
  specialize_arrow ps.ps_vars ps.ps_aty

let specialize_plsymbol pls =
  let htv = Htv.create 3 and hreg = Hreg.create 3 in
  let conv fd = spec_ity htv hreg vars_empty fd.fd_ity in
  List.map conv pls.pl_args, conv pls.pl_value

let dity_of_ty htv hreg vars ty =
  let rec pure ty = match ty.ty_node with
    | Tyapp (ts,tl) ->
        begin try ignore (restore_its ts); false
        with Not_found -> List.for_all pure tl end
    | Tyvar _ -> true in
  if not (pure ty) then raise Exit;
  spec_ity htv hreg vars (ity_of_ty ty)

let specialize_lsymbol ls =
  let htv = Htv.create 3 and hreg = Hreg.create 3 in
  let conv ty = dity_of_ty htv hreg vars_empty ty in
  let ty = Opt.get_def ty_bool ls.ls_value in
  List.map conv ls.ls_args, conv ty

let specialize_lsymbol ls =
  try specialize_lsymbol ls with Exit ->
    Loc.errorm "Function symbol `%a' can only be used in specification"
      Pretty.print_ls ls

(** Patterns *)

type dpattern = {
  dp_pat  : pre_ppattern;
  dp_dity : dity;
  dp_vars : dity Mstr.t;
  dp_loc  : Loc.position option;
}

type dpattern_node =
  | DPwild
  | DPvar  of preid
  | DPlapp of lsymbol * dpattern list
  | DPpapp of plsymbol * dpattern list
  | DPor   of dpattern * dpattern
  | DPas   of dpattern * preid

(** Specifications *)

type ghost = bool

type opaque = Stv.t

type dbinder = preid option * ghost * opaque * dity

type 'a later = vsymbol Mstr.t -> 'a
  (* specification terms are parsed and typechecked after the program
     expressions, when the types of locally bound program variables are
     already established. *)

type dspec = {
  ds_pre     : pre;
  ds_post    : post;
  ds_xpost   : xpost;
  ds_reads   : vsymbol list;
  ds_writes  : term list;
  ds_variant : variant list;
}

type dtype_v =
  | DSpecV of dity
  | DSpecA of dbinder list * dtype_c

and dtype_c = dtype_v * dspec later

(** Expressions *)

type dlazy_op = DEand | DEor

type dexpr = {
  de_node : dexpr_node;
  de_dvty : dvty;
  de_loc  : Loc.position option;
}

and dexpr_node =
  | DEvar of string * dvty
  | DEgpvar of pvsymbol
  | DEgpsym of psymbol
  | DEplapp of plsymbol * dexpr list
  | DElsapp of lsymbol * dexpr list
  | DEapply of dexpr * dexpr list
  | DEconstant of Number.constant
  | DEval of dval_decl * dexpr
  | DElet of dlet_defn * dexpr
  | DEfun of dfun_defn * dexpr
  | DErec of dfun_defn list * dexpr
  | DEif of dexpr * dexpr * dexpr
  | DEmatch of dexpr * (dpattern * dexpr) list
  | DEassign of plsymbol * dexpr * dexpr
  | DElazy of dlazy_op * dexpr * dexpr
  | DEnot of dexpr
  | DEtrue
  | DEfalse
  | DEraise of xsymbol * dexpr
  | DEtry of dexpr * (xsymbol * dpattern * dexpr) list
  | DEfor of preid * dexpr * for_direction * dexpr * invariant later * dexpr
  | DEloop of variant list later * invariant later * dexpr
  | DEabsurd
  | DEassert of assertion_kind * term later
  | DEabstract of dexpr * dspec later
  | DEmark of preid * dexpr
  | DEghost of dexpr
  | DEany of dtype_c
  | DEcast of dexpr * ity
  | DEuloc of dexpr * Loc.position
  | DElabel of dexpr * Slab.t

and dval_decl = preid * ghost * dtype_v

and dlet_defn = preid * ghost * dexpr

and dfun_defn = preid * ghost * dbinder list * dexpr * dspec later

(** Environment *)

type denv = {
  frozen : dity list;
  locals : (Stv.t option * dvty) Mstr.t;
}

let denv_empty = { frozen = []; locals = Mstr.empty }

let is_frozen frozen tv =
  try List.iter (occur_check tv) frozen; false with Exit -> true

let freeze_dvty frozen (argl,res) =
  let rec add l = function
    | Dvar { contents = Dval d } -> add l d
    | Dvar { contents = Dtvs _ } as d -> d :: l
    | Dutv _ as d -> d :: l
    | Dapp (_,tl,_) | Dpur (_,tl) -> List.fold_left add l tl in
  List.fold_left add (add frozen res) argl

let freeze_dtvs frozen (argl,res) =
  let rec add l = function
    | Dvar { contents = Dval d } -> add l d
    | Dvar { contents = Dtvs _ } as d -> d :: l
    | Dutv _ -> l
    | Dapp (_,tl,_) | Dpur (_,tl) -> List.fold_left add l tl in
  List.fold_left add (add frozen res) argl

let free_vars frozen (argl,res) =
  let rec add s = function
    | Dvar { contents = Dval d } -> add s d
    | Dvar { contents = Dtvs tv }
    | Dutv tv -> if is_frozen frozen tv then s else Stv.add tv s
    | Dapp (_,tl,_) | Dpur (_,tl) -> List.fold_left add s tl in
  List.fold_left add (add Stv.empty res) argl

let free_user_vars frozen (argl,res) =
  let rec add s = function
    | Dvar { contents = Dval d } -> add s d
    | Dvar { contents = Dtvs _ } -> s
    | Dutv tv -> if is_frozen frozen tv then s else Stv.add tv s
    | Dapp (_,tl,_) | Dpur (_,tl) -> List.fold_left add s tl in
  List.fold_left add (add Stv.empty res) argl

let denv_add_mono { frozen = frozen; locals = locals } id dvty =
  let locals = Mstr.add id.pre_name (None, dvty) locals in
  { frozen = freeze_dvty frozen dvty; locals = locals }

let denv_add_poly { frozen = frozen; locals = locals } id dvty =
  let ftvs = free_vars frozen dvty in
  let locals = Mstr.add id.pre_name (Some ftvs, dvty) locals in
  { frozen = frozen; locals = locals }

let denv_add_rec { frozen = frozen; locals = locals } id dvty =
  let ftvs = free_user_vars frozen dvty in
  let locals = Mstr.add id.pre_name (Some ftvs, dvty) locals in
  { frozen = freeze_dtvs frozen dvty; locals = locals }

let denv_add_val denv (id,_,dtv) =
  let rec dvty argl = function
    | DSpecA (bl,(dtv,_)) ->
        dvty (List.fold_left (fun l (_,_,_,t) -> t::l) argl bl) dtv
    | DSpecV res -> (List.rev argl, res) in
  denv_add_poly denv id (dvty [] dtv)

let denv_add_let denv (id,_,{de_dvty = dvty}) =
  denv_add_mono denv id dvty

let denv_add_fun denv (id,_,bl,{de_dvty = (argl,res)},_) =
  let argl = List.fold_right (fun (_,_,_,t) l -> t::l) bl argl in
  denv_add_poly denv id (argl, res)

let denv_prepare_rec denv l =
  let add s ({pre_name = n},_,_) =
    Sstr.add_new (Dterm.DuplicateVar n) n s in
  let _ = try List.fold_left add Sstr.empty l with
    | Dterm.DuplicateVar n -> (* TODO: loc *)
        Loc.errorm "duplicate function name %s" n in
  let add denv (id,bl,res) =
    let argl = List.map (fun (_,_,_,t) -> t) bl in
    denv_add_rec denv id (argl, res) in
  List.fold_left add denv l

let denv_verify_rec { frozen = frozen; locals = locals } id =
  let check tv = if is_frozen frozen tv then Loc.errorm (* TODO: loc *)
    "This function is expected to be polymorphic in type variable %a"
    Pretty.print_tv tv in
  match Mstr.find_opt id.pre_name locals with
    | Some (Some tvs, _) -> Stv.iter check tvs
    | Some (None, _) -> assert false
    | None -> assert false

let denv_add_args { frozen = frozen; locals = locals } bl =
  let l = List.fold_left (fun l (_,_,_,t) -> t::l) frozen bl in
  let add s (id,_,_,t) = match id with
    | Some {pre_name = n} ->
        Mstr.add_new (Dterm.DuplicateVar n) n (None, ([],t)) s
    | None -> s in
  let s = List.fold_left add Mstr.empty bl in
  { frozen = l; locals = Mstr.set_union s locals }

let denv_add_pat { frozen = frozen; locals = locals } dp =
  let l = Mstr.fold (fun _ t l -> t::l) dp.dp_vars frozen in
  let s = Mstr.map (fun t -> None, ([], t)) dp.dp_vars in
  { frozen = l; locals = Mstr.set_union s locals }

let mk_node n = function
  | Some tvs, dvty -> DEvar (n, specialize_scheme tvs dvty)
  | None,     dvty -> DEvar (n, dvty)

let denv_get denv n =
  mk_node n (Mstr.find_exn (Dterm.UnboundVar n) n denv.locals)

let denv_get_opt denv n =
  Opt.map (mk_node n) (Mstr.find_opt n denv.locals)

(** Constructors *)

let dpattern ?loc _ = ignore(loc); assert false (* ?loc:Loc.position -> dpattern_node -> dpattern *)

let dexpr ?loc _ = ignore (loc); assert false (* ?loc:Loc.position -> dexpr_node -> dexpr *)

(** Final stage *)

let expr     ~strict ~keep_loc _ = ignore(strict); ignore(keep_loc); assert false (* strict:bool -> keep_loc:bool -> dexpr -> expr *)
let val_decl ~strict ~keep_loc _ = ignore(strict); ignore(keep_loc); assert false (* strict:bool -> keep_loc:bool -> dval_decl -> let_sym *)
let let_defn ~strict ~keep_loc _ = ignore(strict); ignore(keep_loc); assert false (* strict:bool -> keep_loc:bool -> dlet_defn -> let_defn *)
let fun_defn ~strict ~keep_loc _ = ignore(strict); ignore(keep_loc); assert false (* strict:bool -> keep_loc:bool -> dfun_defn -> fun_defn *)
let rec_defn ~strict ~keep_loc _ = ignore(strict); ignore(keep_loc); assert false (* strict:bool -> keep_loc:bool -> dfun_defn list -> fun_defn list *)
