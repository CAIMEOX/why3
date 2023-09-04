(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3
open Wstdlib
open Ident
open Ty
open Term

type hsymbol = {
  hs_name : ident;
}

module Hsym = MakeMSHW (struct
  type t = hsymbol
  let tag hs = hs.hs_name.id_tag
end)

module Shs = Hsym.S
module Mhs = Hsym.M
(*
module Hhs = Hsym.H
module Whs = Hsym.W

let hs_equal : hsymbol -> hsymbol -> bool = (==)
let hs_hash hs = id_hash hs.hs_name
let hs_compare hs1 hs2 = id_compare hs1.hs_name hs2.hs_name
*)

let create_hsymbol id = { hs_name = id_register id }

(*
let t_and_simp = t_and
let t_and_asym_simp = t_and_asym
let t_implies_simp = t_implies
let t_forall_close_simp = t_forall_close
*)

type param =
  | Pt of tvsymbol
  | Pv of vsymbol
  | Pr of vsymbol
  | Pc of hsymbol * vsymbol list * param list

type expr =
  | Esym of hsymbol
  | Eapp of expr * argument
  | Elam of param list * expr
  | Edef of expr * hsymbol * vsymbol list * param list * expr
  | Erec of expr * hsymbol * vsymbol list * param list * expr
  | Easr of term * expr
  | Ebox of expr
  | Ewox of expr
  | Eany

and argument =
  | At of ty
  | Av of term
  | Ar of vsymbol
  | Ac of expr

let arg_of_param = function
  | Pt a -> At (ty_var a)
  | Pv v -> Av (t_var v)
  | Pr r -> Ar r
  | Pc (g,_,_) -> Ac (Esym g)

let fail pl =
  let add e = function
    | Pc (h, wr, pl) ->
        let app d p = Eapp (d, arg_of_param p) in
        let d = List.fold_left app (Esym h) pl in
        Edef (e, h, wr, pl, Ebox d)
    | Pt _ | Pv _ | Pr _ -> e in
  Elam (pl, List.fold_left add (Easr (t_false, Eany)) pl)

type binding =
  | Bt of ty
  | Bv of term
  | Br of term * vsymbol
  | Bc of closure

and closure = bool -> term Mvs.t -> binding list -> term

type context = {
  ctx_tsb : ty Mtv.t;
  ctx_sbs : term Mvs.t;
  ctx_cnt : (vsymbol Mvs.t * closure) Mhs.t;
  ctx_prt : Shs.t; (* empty when ctx_str *)
  ctx_str : bool;
}

let ctx_empty = {
  ctx_tsb = Mtv.empty;
  ctx_sbs = Mvs.empty;
  ctx_cnt = Mhs.empty;
  ctx_prt = Shs.empty;
  ctx_str = true;
}

let t_inst c t = t_ty_subst c.ctx_tsb c.ctx_sbs t
let r_inst c r = t_ty_subst c.ctx_tsb c.ctx_sbs (t_var r)

let ctx_add_t a t c = { c with ctx_tsb = Mtv.add a t c.ctx_tsb }
let ctx_add_v v t c = { c with ctx_sbs = Mvs.add v t c.ctx_sbs }

let ctx_add_c h w m d c = let set w r = Mvs.add r (Mvs.find_def r r m) w in
  { c with ctx_cnt = Mhs.add h (List.fold_left set Mvs.empty w, d) c.ctx_cnt;
           ctx_prt = if c.ctx_str then Shs.empty else Shs.add h c.ctx_prt }

let prepare c s u = { c with
  ctx_sbs = Mvs.set_union u c.ctx_sbs;
  ctx_prt = if s then c.ctx_prt else Shs.empty;
  ctx_str = s && c.ctx_str }

let consume c pl bl =
  let eat (c,m) p b = match p, b with
    | Pt a, Bt t -> ctx_add_t a t c, m
    | Pv v, Bv t -> ctx_add_v v t c, m
    | Pr p, Br (q,r) -> ctx_add_v p q c, Mvs.add p r m
    | Pc (h,w,_), Bc d -> ctx_add_c h w m d c, m
    | _ -> assert false in
  fst (List.fold_left2 eat (c, Mvs.empty) pl bl)

let rec vc pp dd c bl = function
  | Esym h ->
      let wr, vcd = Mhs.find h c.ctx_cnt in
      let prot = c.ctx_str || Shs.mem h c.ctx_prt in
      let conv p q up = Mvs.add q (r_inst c p) up in
      vcd (pp && prot) (Mvs.fold conv wr Mvs.empty) bl
  | Eapp (e, a) ->
      let b = match a with
        | At t -> Bt (ty_inst c.ctx_tsb t)
        | Av t -> Bv (t_inst c t)
        | Ar r -> Br (r_inst c r, r)
        | Ac d -> Bc (fun s u bl -> vc pp dd (prepare c s u) bl d) in
      vc pp dd c (b::bl) e
  | Elam (pl, e) ->
      let c = consume c pl bl in
      let pick_hs s = function
        | Pc (h,_,_) -> Shs.add h s
        | Pt _ | Pv _ | Pr _ -> s in
      let hs = List.fold_left pick_hs Shs.empty pl in
      let cw = { c with ctx_prt = hs; ctx_str = false } in
      t_and_simp (vc pp dd c [] e) (vc (not pp) (not dd) cw [] e)
  | Edef (e, h, wr, pl, d) -> assert (bl = []);
      let vcd s u bl =
        let c = consume (prepare c s u) pl bl in
        vc true false c [] d in
      let cl = ctx_add_c h wr Mvs.empty vcd c in
      let lhs = vc pp dd cl [] e in
      let cr,vl = havoc c wr pl in
      let rhs = vc false pp cr [] d in
      t_and_simp lhs (t_forall_close_simp vl [] rhs)
  | Erec (e, h, wr, pl, d) -> assert (bl = []);
      let vcd s u bl =
        let c = consume (prepare c s u) pl bl in
        let c,_ = havoc c [] [Pc (h, wr, pl)] in
        vc true false c [] d in
      let c = ctx_add_c h wr Mvs.empty vcd c in
      let lhs = vc pp dd c [] e in
      let cr,vl = havoc c wr pl in
      let rhs = vc false pp cr [] d in
      t_and_simp lhs (t_forall_close_simp vl [] rhs)
  | Easr (f, e) -> assert (bl = []);
      (if pp && c.ctx_str then t_and_asym_simp else t_implies_simp)
        (t_inst c f) (vc pp dd c [] e)
  | Ebox e -> assert (bl = []); vc dd dd c [] e
  | Ewox e -> assert (bl = []); vc pp pp c [] e
  | Eany -> assert (bl = []); t_true

and havoc c wr pl =
  let set (c,vl) p =
    let q = Mvs.find p c.ctx_sbs in
    let id = id_clone (match q.t_node with
      | Tvar v -> v | _ -> p).vs_name in
    let r = create_vsymbol id (t_type q) in
    ctx_add_v p (t_var r) c, r::vl in
  let c,vl = List.fold_left set (c,[]) wr in
  let set (c,vl) = function
    | Pt a ->
        ctx_add_t a (ty_var (create_tvsymbol (id_clone a.tv_name))) c, vl
    | Pv v | Pr v ->
        let ty = ty_inst c.ctx_tsb v.vs_ty in
        let u = create_vsymbol (id_clone v.vs_name) ty in
        ctx_add_v v (t_var u) c, u::vl
    | Pc (h,wr,pl) ->
        let vcd s u bl = vc true true (prepare c s u) bl (fail pl) in
        ctx_add_c h wr Mvs.empty vcd c, vl in
  let c,vl = List.fold_left set (c,vl) pl in
  c, List.rev vl

let vc e = vc true true ctx_empty [] e

let (!) h = Esym h

let (--) e t = Eapp (e, At t)
let (-+) e t = Eapp (e, Av t)
let (-&) e r = Eapp (e, Ar r)
let (-*) e d = Eapp (e, Ac d)

let (>>) e (h,wr,pl,d) = Edef (e,h,wr,pl,d)
let (<<) e (h,wr,pl,d) = Erec (e,h,wr,pl,d)

let def h wr pl d = (h,wr,pl,d)
let lam pl d = Elam (pl,d)

let asrt f d = Easr (f,d)

let hs_halt = create_hsymbol (id_fresh "halt")
let hs_fail = create_hsymbol (id_fresh "fail")

let hs_alloc = create_hsymbol (id_fresh "alloc")
let hs_assign = create_hsymbol (id_fresh "assign")

let hs_if = create_hsymbol (id_fresh "if")
let hs_then = create_hsymbol (id_fresh "then")
let hs_else = create_hsymbol (id_fresh "else")

let hs_ret = create_hsymbol (id_fresh "ret")
let hs_out = create_hsymbol (id_fresh "out")
let hs_loop = create_hsymbol (id_fresh "loop")

let vs_ii = create_vsymbol (id_fresh "i") ty_int
(*
let vs_ji = create_vsymbol (id_fresh "j") ty_int
let vs_ki = create_vsymbol (id_fresh "k") ty_int
let vs_li = create_vsymbol (id_fresh "l") ty_int
let vs_mi = create_vsymbol (id_fresh "m") ty_int
*)
let vs_pi = create_vsymbol (id_fresh "p") ty_int
(*
let vs_qi = create_vsymbol (id_fresh "q") ty_int
*)

let vs_bb = create_vsymbol (id_fresh "b") ty_bool

let tv_a = tv_of_string "a"
let vs_ia = create_vsymbol (id_fresh "i") (ty_var tv_a)
let vs_ja = create_vsymbol (id_fresh "j") (ty_var tv_a)
let vs_ka = create_vsymbol (id_fresh "k") (ty_var tv_a)
let vs_la = create_vsymbol (id_fresh "l") (ty_var tv_a)
let vs_ma = create_vsymbol (id_fresh "m") (ty_var tv_a)

let tv_c = tv_of_string "c"
let vs_uc = create_vsymbol (id_fresh "u") (ty_var tv_c)
let vs_vc = create_vsymbol (id_fresh "v") (ty_var tv_c)

let expr1 =
  !hs_alloc -- ty_int -+ t_nat_const 3 -* (lam [Pr vs_pi]
    !hs_loop -- ty_int -+ t_var vs_pi -* !hs_out -+
                              t_nat_const 3 -+ t_nat_const 0 -+ t_nat_const 5
    << def hs_loop [vs_pi] [Pt tv_a; Pv vs_ia; Pc (hs_ret,[vs_pi],[Pv vs_ja]);
                                                Pv vs_ka; Pv vs_la; Pv vs_ma]
          (asrt (t_and (t_neq (t_var vs_ia) (t_var vs_ka))
                   (t_neq (t_var vs_pi) (t_nat_const 9)))
          (Ebox (!hs_if -+ (t_if (t_equ (t_var vs_ia) (t_var vs_la))
                                t_bool_true t_bool_false) -*
             (lam [] (!hs_assign -- ty_int -& vs_pi -+ t_nat_const 2 -*
                (lam [] (!hs_loop -- ty_var tv_a -+ t_var vs_ia -* !hs_ret
                  -+ t_var vs_la -+ t_var vs_ma -+ t_var vs_ka)))) -*
             (lam [] (!hs_ret -+ t_var vs_ia))))
        >> def hs_ret [vs_pi] [Pv vs_ja]
          (asrt (t_and (t_equ (t_var vs_ma) (t_var vs_ja))
                       (t_equ (t_nat_const 55) (t_var vs_pi)))
                                   (Ebox (!hs_ret -+ t_var vs_ja))))
    >> def hs_out [vs_pi] [Pv vs_ii]
      (asrt (t_and (t_equ (t_var vs_ii) (t_nat_const 42))
                   (t_equ (t_var vs_pi) (t_nat_const 37))) (Ebox !hs_halt)))
  >> def hs_assign [] [Pt tv_c; Pr vs_uc; Pv vs_vc; Pc (hs_ret,[vs_uc],[])]
      (Eany >> def hs_ret [vs_uc] [] (asrt (t_equ (t_var vs_uc) (t_var vs_vc))
                                              (Ebox (!hs_ret))))
  >> def hs_alloc [] [Pt tv_c; Pv vs_vc; Pc (hs_ret,[],[Pr vs_uc])]
      (Eany >> def hs_ret [] [Pr vs_uc] (asrt (t_equ (t_var vs_uc) (t_var vs_vc))
                                              (Ebox (!hs_ret -& vs_uc))))
  >> def hs_if [] [Pv vs_bb; Pc (hs_then,[],[]); Pc (hs_else,[],[])]
      (Eany >> def hs_then [] [] (asrt (t_equ (t_var vs_bb) t_bool_true) (Ebox !hs_then))
            >> def hs_else [] [] (asrt (t_equ (t_var vs_bb) t_bool_false) (Ebox !hs_else)))
  >> def hs_fail [] [] (asrt t_false Eany)
  >> def hs_halt [] [] (Ewox Eany)

(*
type env = {
  ps_int_le : lsymbol;
  ps_int_ge : lsymbol;
  ps_int_lt : lsymbol;
  ps_int_gt : lsymbol;
  fs_int_pl : lsymbol;
  fs_int_mn : lsymbol;
}

let mk_env {Theory.th_export = ns_int} = {
  ps_int_le = Theory.ns_find_ls ns_int [op_infix "<="];
  ps_int_ge = Theory.ns_find_ls ns_int [op_infix ">="];
  ps_int_lt = Theory.ns_find_ls ns_int [op_infix "<"];
  ps_int_gt = Theory.ns_find_ls ns_int [op_infix ">"];
  fs_int_pl = Theory.ns_find_ls ns_int [op_infix "+"];
  fs_int_mn = Theory.ns_find_ls ns_int [op_infix "-"];
}
*)

let mk_goal tuc s e =
  let prs = Decl.create_prsymbol (id_fresh ("vc_" ^ s)) in
  let vcf = vc e in
  Format.printf "@[%a@]@." Pretty.print_term vcf;
  Theory.add_prop_decl tuc Decl.Pgoal prs vcf

let read_channel env path _file _c =
(*
  let ast = Coma_lexer.parse file c in
  Format.printf "@[%a@]@." (fun fmt l ->
    List.iter (fun d -> Coma_syntax.print_decl fmt d) l) ast;
*)
  let th_int = Env.read_theory env ["int"] "Int" in
  let tuc = Theory.create_theory ~path (id_fresh "Coma") in
  let tuc = Theory.use_export tuc Theory.bool_theory in
  let tuc = Theory.use_export tuc th_int in
  let tuc = mk_goal tuc "expr1" expr1 in
  Mstr.singleton "Coma" (Theory.close_theory tuc)

let () = Env.register_format Env.base_language "coma" ["coma"] read_channel
  ~desc:"Continuation Machine language"
