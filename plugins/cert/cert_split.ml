(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3


open Ident
open Ty
open Term
open Decl

open Cert_certificates

let rec rename_vcert pr1 pr2 c =
  propagate_cert (rename_vcert pr1 pr2)
    (fun pr -> if pr_equal pr pr1 then pr2 else pr)
    (fun ct -> ct) c

let rename_cert pr1 pr2 (l, c) =
  l, rename_vcert pr1 pr2 c

type split = {
  right_only : bool;
  (* split only the right side every time. This makes split more efficient
     while preserving most use cases : we mostly want to split on the goal which
     is on the right of implications *)
  byso_split : bool;
  (* do we eliminate by and so constructions during the split *)
  side_split : bool;
  stop_split : bool;
  (* do we stop at a Term.stop_split *)
  cpos_split : bool;
  cneg_split : bool;
  asym_split : bool;
  intro_mode : bool;
  comp_match : known_map option;
}

let stop f = Sattr.mem Term.stop_split f.t_attrs
(* remember that the Term.stop_split attribute is set on requires and ensures for example :
   a first call to split with stop_split on makes it clear where proof obligations comme from
   a second call to split will completely split the formulas *)
let asym f = Sattr.mem Term.asym_split f.t_attrs
(* remember that A /\ B and A && B are both represented by t_or (A, B), the distinction
   between the 2 comes from the attribute Term.asym_split on A *)

let case_split = Ident.create_attribute "case_split"
let case f = Sattr.mem case_split f.t_attrs

let compiled = Ident.create_attribute "split_goal: compiled match"

let unstop f =
  t_attr_set ?loc:f.t_loc (Sattr.remove stop_split f.t_attrs) f

let print_pr_t fmt (pr, t) =
  Format.fprintf fmt "[%a : %a]"
    Pretty.print_pr pr
    Pretty.print_term t


(* Represent monoid of formula interpretation for conjonction and disjunction *)
module M = struct

  (* Multiplication tree *)
  type 'a comb = Base of 'a | Op of 'a comb * 'a comb

  (* zero: false for /\, true for \/
     unit: true for /\, false for \/ *)
  type 'a monoid = Zero of 'a | Unit | Comb of 'a comb

  (* Triviality degree. *)
  let degree = function Unit -> 0 | Zero _ | Comb (Base _) -> 1 | _ -> 2

  (* inject formula into monoid. *)
  let (!+) a = Comb (Base a)

  (* monoid law. *)
  let (++) a b =
    match a, b with
    | _, Unit | Zero _, _ -> a
    | Unit, _ | _, Zero _ -> b
    | Comb ca, Comb cb -> Comb (Op (ca, cb))

  (* (base -> base) morphism application. *)
  let rec cmap f = function
    | Base a -> Base (f a)
    | Op (a,b) -> Op (cmap f a, cmap f b)

  (* (base -> general) morphism application *)
  let rec cbind f = function
    | Base a -> f a
    | Op (a,b) -> Op (cbind f a, cbind f b)

  (* Apply morphism phi from monoid 1 to monoid 2
     (law may change)
     Implicit morphism phi must respect:
     phi(zero_1) = f0 (term representing the zero)
     phi(unit_1) = unit_2
     phi(x `law_1` y) = phi(x) `law_2` phi(y)
     phi(a) = f a (for base values, and f a is a base value)
     Intended: monotone context closure, negation *)
  let map f0 f = function
    | Zero t -> f0 t
    | Unit -> Unit
    | Comb c -> Comb (cmap f c)

  (* Apply bimorphism phi from monoids 1 and 2 to monoid 3
     Implicit bimorphism phi must respect:
     - partial applications of phi (phi(a,_) and phi(_,b)) are morphisms
     - phi(zero,b) = f0_ 'term for zero' b (for b a base value,
                                            f0_ _ b is a base value)
     - phi(a,zero) = f_0 'term for zero' a (for a a base value,
                                            f_0 a _ is a base value)
     - phi(zero,zero) = f00 'term for first zero' 'term for second zero'
     - phi(a,b) = f a b (for a,b base value, and f a b is a base value)
     Intended: mainly /\, \/ and ->
   *)
  let bimap f00 f0_ f_0 f a b = match a, b with
    | Unit, _ | _, Unit -> Unit
    | Zero t1, Zero t2 -> f00 t1 t2
    | Zero t1, Comb cb -> Comb (cmap (f0_ t1) cb)
    | Comb ca, Zero t2 -> Comb (cmap (f_0 t2) ca)
    | Comb ca, Comb cb -> Comb (cbind (fun x -> cmap (f x) cb) ca)

  let rec to_list m acc = match m with
    | Base a -> a :: acc
    | Op (a,b) -> to_list a (to_list b acc)

  let to_list = function
    | Zero t -> [t]
    | Unit -> []
    | Comb c -> to_list c []

  let print_mon sep fmt c =
    Pp.print_list
      (fun fmt () -> Format.fprintf fmt "%s" sep)
      print_pr_t
      fmt
      (to_list c)

end

type 'a split_ret = {
  (* Conjunctive decomposition of formula f *)
  conj : 'a M.monoid;
  (* Certificate to decompose f as a Conjunction in Positive position :
     cp ⇓ (⊢ f) ≜  [⊢ conjᵢ]ᵢ *)
  cp : visible_cert;
  (* Certificate to decompose f as a Conjunction in Negative position :
     cn ⇓ (f ⊢) ≜ [conj₁, ..., conjₙ ⊢] *)
  (* WARNING : the previous equality is only valid when byso_split is off *)
  cn : visible_cert;
  (* Disjunctive decomposition of formula f *)
  disj : 'a M.monoid;
  (* Certificate to decompose f as a Disjunction in Negative position :
     dn ⇓ (f ⊢) ≜  [disjᵢ ⊢]ᵢ*)
  dn : visible_cert;
  (* Certificate to decompose f as a Disjunction in Positive position :
     dp ⇓ (⊢ f) ≜  [⊢ disj₁, ..., disjₙ] *)
  (* WARNING : the previous equality is only valid when byso_split is off *)
  dp : visible_cert;
  (* Backward pull of formula: bwd ⇒ f (typically from by) *)
  bwd : 'a;
  (* Forward pull of formula : f ⇒ fwd (typically from so) *)
  fwd : 'a;
  (* Side-condition (generated from by/so occurrences when byso_split is on) *)
  side : 'a M.monoid;
  (* Indicate whether positive/negative occurrences of formula force decomposition. *)
  cpos : bool;
  cneg : bool;
}

let print_ret_err { conj; cp; cn; disj; dn; dp; bwd; fwd; side; cpos; cneg } =
  Format.fprintf Format.err_formatter
    "@[<h>\
     conj  : @[%a@]@\n\
     cp    : @[%a@]@\n\
     cn    : @[%a@]@\n\
     disj  : @[%a@]@\n\
     dn    : @[%a@]@\n\
     dp    : @[%a@]@\n\
     bwd   : @[%a@]@\n\
     fwd   : @[%a@]@\n\
     side  : @[%a@]@\n\
     cpos  : %b@\n\
     cneg  : %b@\n@]@."
    (M.print_mon " /\\ ") conj
    prcertif cp
    prcertif cn
    (M.print_mon " \\/ ") disj
    prcertif dn
    prcertif dp
    print_pr_t bwd
    print_pr_t fwd
    (M.print_mon " /\\ ") side
    cpos
    cneg

let rec drop_byso f = match f.t_node with
  | Tbinop (Timplies,{ t_node = Tbinop (Tor,_,{ t_node = Ttrue }) },f) ->
      drop_byso f
  | Tbinop (Tand,f,{ t_node = Tbinop (Tor,_,{ t_node = Ttrue }) }) ->
      drop_byso f
  | _ -> t_map drop_byso f


open M

let pat_condition kn tv cseen p =
  match p.pat_node with
  | Pwild ->
      let csl,sbs = match p.pat_ty.ty_node with
        | Tyapp (ts,_) ->
            Decl.find_constructors kn ts,
            let ty = ty_app ts (List.map ty_var ts.ts_args) in
            ty_match Mtv.empty ty p.pat_ty
        | _ -> assert false in
      let csall = Sls.of_list (List.rev_map fst csl) in
      let csnew = Sls.diff csall cseen in
      assert (not (Sls.is_empty csnew));
      let add_cs cs g =
        let mk_v ty = create_vsymbol (id_fresh "w") (ty_inst sbs ty) in
        let vl = List.map mk_v cs.ls_args in
        let f = t_equ tv (fs_app cs (List.map t_var vl) p.pat_ty) in
        g ++ !+ (t_exists_close_simp vl [] f) in
      let g = Sls.fold add_cs csnew Unit in
      csall, [], g
  | Papp (cs, pl) ->
      let vl = List.map (function
        | {pat_node = Pvar v} -> v | _ -> assert false) pl in
      let g = t_equ tv (fs_app cs (List.map t_var vl) p.pat_ty) in
      Sls.add cs cseen, vl, !+g
  | _ -> assert false

let rec fold_cond = function
  | Base a -> a
  | Op (a,b) -> t_or (fold_cond a) (fold_cond b)

let fold_cond = function
  | Comb c -> !+(fold_cond c)
  | x -> x

let destruct_reconstruct pr pr1 pr2 c1 c2 =
  lambda One (fun i -> Destruct (pr, pr1, pr2, Hole i))
  |>> c1
  |>> c2
  |>> lambda One (fun i -> Construct (pr1, pr2, pr, Hole i))

let luop op (pr, t) = pr, op t

let lbop op (_, t1) (_, t2) =
  let pr = create_prsymbol (id_fresh "binop") in
  pr, op t1 t2


let rec split_core sp pr f : (prsymbol * term) split_ret =
  let (~-) = t_attr_copy f in
  let ro = sp.right_only in
  let alias fo1 unop f1 =
    if fo1 == f1 then f else - unop f1 in
  let alias2 fo1 fo2 binop f1 f2 =
    if fo1 == f1 && fo2 == f2 then f else - binop f1 f2 in
  let rec trivial n = function
    | x :: q -> let m = n + degree x in (m <= 1 && trivial m q)
    | [] -> true in
  let trivial bs = trivial 0 bs in
  let pcaset bs sf =
    let test = not ro || (sf.cpos && trivial bs) in
    (if test then sf.conj else !+(sf.bwd)), test in
  let pcase bs sf = let x, _ = pcaset bs sf in x in
  let ncaset bs sf =
    let test = not ro || (sf.cneg && trivial bs) in
    (if test then sf.disj else !+(sf.fwd)), test in
  let ncase bs sf = let x, _ = ncaset bs sf in x in
  let ps_csp sp = { sp with cpos_split = false } in
  let ng_csp sp = { sp with cneg_split = false } in
  let no_csp sp = { sp with cpos_split = false;
                            cneg_split = false } in
  let in_csp sp = { sp with cpos_split = sp.cneg_split;
                            cneg_split = sp.cpos_split } in
  let ngt _ (pr, t) = pr, t_not t and cpy _ (pr, t) = pr, t in
  let bimap = bimap (fun _ t -> Zero t) cpy in
  let iclose = bimap ngt (lbop t_implies) in
  let aclose = bimap cpy (lbop t_and) in
  let nclose ps = map (fun (pr, t) -> Zero (pr, t_attr_copy t t_true)) (luop t_not) ps in
  let ret conj cp cn  disj dn dp bwd fwd side cpos cneg =
      { conj; cp; cn; disj; dn; dp; bwd; fwd; side; cpos; cneg } in
  let r = match f.t_node with
  | _ when sp.stop_split && stop f ->
      let df = drop_byso f in
      ret !+(pr, unstop f) (hole ()) nc
        !+(pr, unstop df) (hole ()) nc
        (pr, f) (pr, df) Unit false false
  | Tbinop (Tiff,_,_) | Tif _ | Tcase _ | Tquant _ when sp.intro_mode ->
      let df = drop_byso f in
      ret !+(pr, f) (hole ()) nc
        !+(pr, df) (hole ()) nc
        (pr, f) (pr, df) Unit false false
  | Ttrue -> ret Unit (lambda Z (Trivial pr)) nc
               (Zero (pr, f)) (lambda One (fun i -> Weakening (pr, Hole i))) nc
               (pr, f) (pr, f) Unit false false
  | Tfalse -> ret (Zero (pr, f)) (lambda One (fun i -> Weakening (pr, Hole i))) nc
                Unit (lambda Z (Trivial pr)) nc
                (pr, f) (pr, f) Unit false false
  | Tapp _ -> let uf = !+(pr, f) in
              ret uf (hole ()) nc
                uf (hole ()) nc
                (pr, f) (pr, f) Unit false false
    (* f1 so f2 *)
  | Tbinop (Tand,f1,{ t_node = Tbinop (Tor,f2,{ t_node = Ttrue }) }) ->
      if not (sp.byso_split && asym f2) then split_core sp pr f1 else
      let (&&&) (_, f1) (_, f2) =
        let pr = create_prsymbol (id_fresh "split_and") in
        pr, - t_and f1 f2 in
      let rc = split_core (no_csp sp) in
      let sf1 = rc pr f1 and sf2 = rc pr f2 in
      let fwd = sf1.fwd &&& sf2.fwd in
      let nf2, cn2 = ncaset [] sf2 in
      let nf1, cn1 = ncaset [nf2;sf2.side;sf2.conj] sf1 in
      let disj = bimap cpy (&&&) nf1 nf2 in
      let close = iclose nf1 in
      let lside = if sp.side_split then close sf2.conj else
        !+(lbop t_implies sf1.fwd sf2.bwd) in
      let side = sf1.side ++ lside ++ close sf2.side in
      ret sf1.conj nc nc
        disj nc nc
        sf1.bwd fwd side sf1.cpos (cn1 || cn2)
  | Tbinop (Tand,f1,f2) ->
      let (&&&) = lbop (alias2 f1 f2 t_and) in
      let rc = split_core (ps_csp sp) in
      let pr1 = create_prsymbol (id_fresh "pr1") in
      let pr2 = create_prsymbol (id_fresh "pr2") in
      let sf1 = rc pr1 f1 and sf2 = rc pr2 f2 in
      let fwd = sf1.fwd &&& sf2.fwd and bwd = sf1.bwd &&& sf2.bwd in
      let asym = sp.asym_split && asym f1 in
      let nf2, cn2 = ncaset [] sf2 in
      let sd = if asym then [sf2.side] else [] in
      let dp = nf2::sd in
      let nf1, cn1 = ncaset dp sf1 in
      let disj = bimap cpy (&&&) nf1 nf2 in
      let conj2 = if not asym then sf2.conj else
        let nf1 = ncase (sf2.conj::sd) sf1 in iclose nf1 sf2.conj in
      let conj = sf1.conj ++ conj2 in
      let side = sf1.side ++ if not asym then sf2.side else
        let nf1 = ncase (sf2.conj::dp) sf1 in iclose nf1 sf2.side in
      let cp = lambda Two (fun i j -> Split (pr, Hole i, Hole j))
               |>>> [rename_cert pr1 pr sf1.cp; rename_cert pr2 pr sf2.cp] in
      let cn = lambda One (fun i -> Destruct (pr, pr1, pr2, Hole i))
               |>> sf1.cn |>> sf2.cn in
      let dn = destruct_reconstruct pr pr1 pr2 sf1.dn sf2.dn in
      let dp = lambda One (fun i ->
               Split (pr,
                      Hole i,
                      Hole i
                 )) in

      ret conj cp cn
        disj dn dp
        bwd fwd side false (cn1 || cn2)
    (* f1 by f2 *)
  | Tbinop (Timplies,{ t_node = Tbinop (Tor,f2,{ t_node = Ttrue }) },f1) ->
      if not (sp.byso_split && asym f2) then split_core sp pr f1 else
      let rc = split_core (no_csp sp) in
      let sf1 = rc pr f1 and sf2 = rc pr f2 in
      let close = iclose (ncase [sf1.conj;sf1.side] sf2) in
      let lside = if sp.side_split then close sf1.conj else
        !+(lbop t_implies sf2.fwd sf1.bwd) in
      let side = sf2.side ++ lside ++ sf1.side in
      ret sf2.conj nc nc sf1.disj nc nc sf2.bwd sf1.fwd side sf2.cpos sf1.cneg
  | Tbinop (Timplies,f1,f2) ->
      let (>->) = lbop (alias2 f1 f2 t_implies) in
      let sp2 = ng_csp sp in let sp1 = in_csp sp2 in
      let sf1 = split_core sp1 pr f1 and sf2 = split_core sp2 pr f2 in
      let fwd = sf1.bwd >-> sf2.fwd and bwd = sf1.fwd >-> sf2.bwd in
      let asym = sp.asym_split && asym f1 in
      let sd = [sf2.side] in
      let disj1 = nclose sf1.conj in
      let disj2 = if not asym then sf2.disj else
        let nf1 = ncase (sf2.disj::sd) sf1 in
        aclose nf1 sf2.disj in
      let disj = disj1 ++ disj2 in
      let dp = sf2.conj::sd in
      let nf1, cn1 = ncaset dp sf1 in
      let conj = bimap (fun _ (pr, a) -> pr, - t_not a) (>->) nf1 sf2.conj in
      let nf1 = ncase (if asym then sf2.disj::dp else dp) sf1 in
      let side = sf1.side ++ iclose nf1 sf2.side in
      ret conj nc nc disj nc nc bwd fwd side (cn1 || sf2.cpos) false
  | Tbinop (Tor,f1,f2) ->
      let (|||) = lbop (alias2 f1 f2 t_or) in
      let rc = split_core (ng_csp sp) in
      let pr1 = create_prsymbol (id_fresh "pr1") in
      let pr2 = create_prsymbol (id_fresh "pr2") in
      let sf1 = rc pr1 f1 and sf2 = rc pr2 f2 in
      let fwd = sf1.fwd ||| sf2.fwd and bwd = sf1.bwd ||| sf2.bwd in
      let asym = sp.asym_split && asym f1 in
      let sd = if asym then [sf2.side] else [] in
      let pf2, cp2 = pcaset [] sf2 in
      let dp = sf2.conj::sd in
      let pf1, cp1 = pcaset dp sf1 in
      let conj = bimap cpy (|||) pf1 pf2 in
      let disj2 = if not asym then sf2.disj else
        let pf1 = pcase (sf2.disj::sd) sf1 in aclose (nclose pf1) sf2.disj in
      let side2 = if not asym then sf2.side else
        let pf1 = pcase (sf2.disj::dp) sf1 in
        bimap cpy (|||) pf1 sf2.side in
      let cp = destruct_reconstruct pr pr1 pr2 sf1.cp sf2.cp in
      let dn = lambda Two (fun i j -> Split (pr, Hole i, Hole j))
               |>>> [sf1.dn; sf2.dn] in
      ret conj cp nc (sf1.disj ++ disj2) dn nc bwd fwd (sf1.side ++ side2) (cp1 || cp2) false
  | Tbinop (Tiff,f1,f2) ->
      let rc = split_core (no_csp sp) in
      let pr1 = create_prsymbol (id_fresh "pr1") in
      let pr2 = create_prsymbol (id_fresh "pr2") in
      let sf1 = rc pr1 f1 and sf2 = rc pr2 f2 in
      let df = if sf1.fwd == sf1.bwd && sf2.fwd == sf2.bwd
        then lbop (alias2 f1 f2 t_iff) sf1.fwd sf2.fwd else pr, drop_byso f in
      let nf1 = ncase [sf2.conj] sf1 and nf2 = ncase [sf1.conj] sf2 in
      let conj = iclose nf1 sf2.conj ++ iclose nf2 sf1.conj in
      let nf2 = ncase [] sf2 and pf2 = pcase [] sf2 in
      let nf1 = ncase [nf2] sf1 and pf1 = pcase [pf2] sf1 in
      let disj_top = aclose nf1 nf2 in
      let disj_bot = aclose (nclose pf1) (nclose pf2) in
      ret conj nc nc (disj_top ++ disj_bot) nc nc df df (sf1.side ++ sf2.side) false false
  | Tif (fif,fthen,felse) ->
      let rc = split_core (no_csp sp) in
      let sfi = rc pr fif and sft = rc pr fthen and sfe = rc pr felse in
      let dfi = if sfi.fwd == sfi.bwd then snd sfi.fwd else drop_byso fif in
      let rebuild fif2 fthen2 felse2 =
        if fif == fif2 && fthen == fthen2 && felse == felse2 then f else
          - t_if fif2 fthen2 felse2
      in
      let fwd = pr, rebuild dfi (snd sft.fwd) (snd sfe.fwd) in
      let bwd = pr, rebuild dfi (snd sft.bwd) (snd sfe.bwd) in
      let sdt = [sft.side] and sde = [sfe.side] in
      let spt = sft.conj::sdt and spe = sfe.conj::sde in
      let nfi = ncase spt sfi and pfi = pcase spe sfi in
      let conj = iclose nfi sft.conj ++ iclose (nclose pfi) sfe.conj in
      let nfi = ncase (sft.disj::sdt) sfi and pfi = pcase (sfe.disj::sde) sfi in
      let disj = aclose nfi sft.disj ++ aclose (nclose pfi) sfe.disj in
      let nfi = ncase (sft.disj::spt) sfi and pfi = pcase (sfe.disj::spe) sfi in
      let eside = iclose (nclose pfi) sfe.side in
      let side = sfi.side ++ iclose nfi sft.side ++ eside in
      ret conj nc nc disj nc nc bwd fwd side false false
  | Tnot f1 ->
      let sf = split_core (in_csp sp) pr f1 in
      let (!) = luop (alias f1 t_not) in
      let (|>) zero = map (fun (pr, t) -> !+(pr, t_attr_copy t zero)) (!) in
      let conj = t_false |> sf.disj and disj = t_true |> sf.conj in
      let cp = lambda One (fun i -> Swap (pr, Hole i))
               |>> sf.dn
               |>> lambda One (fun i -> Swap (pr, Hole i)) in
      let dn = lambda One (fun i -> Swap (pr, Hole i))
               |>> sf.cp
               |>> lambda One (fun i -> Swap (pr, Hole i)) in
      ret conj cp nc
        disj dn nc
        !(sf.fwd) !(sf.bwd) sf.side sf.cneg sf.cpos
  | Tlet (t,fb) ->
      let vs, f1 = t_open_bound fb in
      let (!) = luop (alias f1 (t_let_close vs t)) in
      let sf = split_core sp pr f1 in
      let (!!) = map (fun t -> Zero t) (!) in
      ret !!(sf.conj) nc nc !!(sf.disj) nc nc !(sf.bwd) !(sf.fwd) !!(sf.side) sf.cpos sf.cneg
  (* | Tcase (t,bl) ->
   *     let rc = match bl with
   *       | [_] -> split_core sp
   *       | _   -> split_core (no_csp sp) in
   *     let k join =
   *       let case_close bl2 =
   *         if Lists.equal (==) bl bl2 then f else - t_case t bl2 in
   *       let sbl = List.map (fun b ->
   *         let p, f, close = t_open_branch_cb b in
   *         p, close, rc pr f) bl in
   *       let blfwd = List.map (fun (p, close, sf) -> close p (snd sf.fwd)) sbl in
   *       let fwd = case_close blfwd in
   *       let blbwd = List.map (fun (p, close, sf) -> close p (snd sf.bwd)) sbl in
   *       let bwd = case_close blbwd in
   *       let conj, disj, side = join sbl in
   *       ret conj nc nc disj nc nc bwd fwd side false false
   *     in
   *     begin match sp.comp_match with
   *     | None ->
   *         let join sbl =
   *           let rec zip_all bf_top bf_bot = function
   *             | [] -> Unit, Unit, Unit, [], []
   *             | (p, close, sf) :: q ->
   *               let c_top = close p t_true and c_bot = close p t_false in
   *               let dp_top = c_top :: bf_top and dp_bot = c_bot :: bf_bot in
   *               let conj, disj, side, af_top, af_bot = zip_all dp_top dp_bot q in
   *               let fzip bf af mid =
   *                 - t_case t (List.rev_append bf (close p mid::af)) in
   *               let zip bf mid af =
   *                 map (fun t -> !+(fzip bf af t)) (fzip bf af) mid in
   *               zip bf_top sf.conj af_top ++ conj,
   *               zip bf_bot sf.disj af_bot ++ disj,
   *               zip bf_top sf.side af_top ++ side,
   *               c_top :: af_top,
   *               c_bot :: af_bot
   *           in
   *           let conj, disj, side, _, _ = zip_all [] [] sbl in
   *           conj, disj, side
   *         in
   *         k join
   *     | Some kn ->
   *         if Sattr.mem compiled f.t_attrs
   *         then
   *           (\* keep the attributes for single-case match *\)
   *           let attrs = match bl with
   *             | [_] -> Sattr.remove case_split
   *                   (Sattr.remove compiled f.t_attrs)
   *             | _ -> Sattr.empty in
   *           let join sbl =
   *             let vs = create_vsymbol (id_fresh "q") (t_type t) in
   *             let tv = t_var vs in
   *             let (~-) fb =
   *               t_attr_set ?loc:f.t_loc attrs (t_let_close_simp vs t fb) in
   *             let _, conj, disj, side =
   *               List.fold_left (fun (cseen, conj, disj, side) (p, _, sf) ->
   *                 let cseen, vl, cond = pat_condition kn tv cseen p in
   *                 let cond = if ro then fold_cond cond else cond in
   *                 let fcl t = - t_forall_close_simp vl [] t in
   *                 let ecl t = - t_exists_close_simp vl [] t in
   *                 let ps cond f = fcl (t_implies cond f) in
   *                 let ng cond f = ecl (t_and cond f) in
   *                 let ngt _ a = fcl (t_not a) and tag _ a = ecl a in
   *                 let conj  = conj ++ bimap ngt ps cond sf.conj  in
   *                 let disj  = disj ++ bimap tag ng cond sf.disj  in
   *                 let side = side ++ bimap ngt ps cond sf.side in
   *                 cseen, conj, disj, side
   *               ) (Sls.empty, Unit, Unit, Unit) sbl
   *             in
   *             conj, disj, side
   *           in
   *           k join
   *         else
   *           let mk_let = t_let_close_simp in
   *           let mk_case t bl = t_attr_add compiled (t_case_close t bl) in
   *           let mk_b b = let p, f = t_open_branch b in [p], f in
   *           let bl = List.map mk_b bl in
   *           rc (- Pattern.compile_bare ~mk_case ~mk_let [t] bl)
   *     end *)
  | Tcase _ -> failwith "TODO"
  | Tquant (qn,fq) ->
      let vsl, trl, f1 = t_open_quant fq in
      let close = luop (alias f1 (t_quant_close qn vsl trl)) in
      let sf = split_core sp pr f1 in
      let bwd = close sf.bwd and fwd = close sf.fwd in
      let conj, disj, cpos, cneg = match qn with
        | Tforall ->
            map (fun t -> Zero t) close sf.conj, !+fwd,
            sf.cpos, false
        | Texists ->
            !+bwd, map (fun t -> Zero t) close sf.disj,
            false, sf.cneg
      in
      let side = map (fun t -> Zero t) (luop (t_forall_close vsl trl)) sf.side in
      ret conj nc nc disj nc nc bwd fwd side cpos cneg
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)
  in
  let r = if case f then
    { r with cpos = sp.cpos_split; cneg = sp.cneg_split } else r in
  match r with
  | { side = M.Zero _ } ->
      { r with conj = Unit; disj = Unit; fwd = pr, t_false; bwd = pr, t_true }
  | _ -> r

let split_core sp pr t =
  let res = split_core sp pr t in
  print_ret_err res;
  res

let full_split kn = {
  right_only = false;
  byso_split = false;
  side_split = true;
  stop_split = false;
  cpos_split = true;
  cneg_split = true;
  asym_split = true;
  intro_mode = false;
  comp_match = kn;
}

let right_split kn = { (full_split kn) with right_only = true }
let full_proof  kn = { (full_split kn) with stop_split = true;
                                            byso_split = true }
let right_proof kn = { (full_proof kn) with right_only = true }
let full_intro  kn = { (full_split kn) with asym_split = false;
                                            intro_mode = true;
                                            stop_split = true }
let right_intro kn = { (full_intro kn) with right_only = true }


let clues = ref []

let reset () = clues := []
let add c = clues := c :: !clues
let pop () = match !clues with
  | h::t -> clues := t; h
  | _ -> assert false

(* let split_conj sp f =
 *   let core = split_core sp f in
 *   assert (core.side = Unit);
 *   to_list core.conj *)

let split_conj sp pr f = (* only used by split_axiom *)
  let core = split_core sp pr f in
  assert (core.side = Unit);
  add (core.cn);
  to_list core.conj

(* let split_proof sp f =
 *   let core = split_core sp f in
 *   to_list (core.conj ++ core.side) *)

let split_proof sp pr f =
  let core = split_core sp pr f in
  add (core.cp);
  to_list (core.conj ++ core.side)

let split_goal sp pr f =
  let make_prop (pr, f) = [create_prop_decl Pgoal pr f] in
  List.map make_prop (split_proof sp pr f)

let split_axiom sp pr f =
  let sp = { sp with asym_split = false; byso_split = false } in
  List.map (fun (pr, f) -> create_prop_decl Paxiom pr f) (split_conj sp pr f)

let split_all sp d = match d.d_node with
  | Dprop (Pgoal, pr,f) -> split_goal sp pr f
  | Dprop (Paxiom,pr,f) -> [split_axiom sp pr f]
  | _ -> [[d]]

let split_premise sp d = match d.d_node with
  | Dprop (Paxiom,pr,f) -> split_axiom sp pr f
  | _ -> [d]

(* let prep_goal split = Trans.store (fun t ->
 *   let split = split (Some (Task.task_known t)) in
 *   let trans = Trans.goal_l (split_goal split) in
 *   Trans.apply trans t) *)

let rev_append_cert lc =
  List.fold_left (|>>) (hole ()) (List.rev lc)

let prep_goal split = Trans.store (fun t ->
  let split = split (Some (Task.task_known t)) in
  reset ();
  let trans = Trans.goal_l (split_goal split) in
  let nt = Trans.apply trans t in
  let cert = rev_append_cert !clues in
  nt, cert)

(* let prep_all split = Trans.store (fun t ->
 *   let split = split (Some (Task.task_known t)) in
 *   let trans = Trans.decl_l (split_all split) None in
 *   Trans.apply trans t) *)

let prep_all split = Trans.store (fun t ->
  let split = split (Some (Task.task_known t)) in
  reset ();
  let trans = Trans.decl_l (split_all split) None in
  let nt = Trans.apply trans t in
  (* List.iter (printf "%a@." (fun _ -> prc err_formatter)) (List.rev !clues); *)
  (* prc err_formatter cert; *)
  (* Format.printf "NUMBER OF CLUES : %d@." (List.length !clues); *)
  nt, rev_append_cert !clues)

(* let prep_premise split = Trans.store (fun t ->
 *   let split = split (Some (Task.task_known t)) in
 *   let trans = Trans.decl (split_premise split) None in
 *   Trans.apply trans t) *)

let prep_premise split = Trans.store (fun t ->
  let split = split (Some (Task.task_known t)) in
  reset ();
  let trans = Trans.decl (split_premise split) None in
  let nt = Trans.apply trans t in
  [nt], rev_append_cert !clues)


let split_goal_full  = prep_goal full_proof
let split_goal_right = prep_goal right_proof

let split_all_full  = prep_all full_proof
let split_all_right = prep_all right_proof

let split_premise_full  = prep_premise full_proof
let split_premise_right = prep_premise right_proof

