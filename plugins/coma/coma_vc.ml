open Why3
open Wstdlib
open Ident
open Ty
open Term
open Coma_syntax

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

(*
let t_and_simp = t_and
let t_and_asym_simp = t_and_asym
let t_implies_simp = t_implies
let t_forall_close_simp = t_forall_close
*)

type wpsp = {
  wp: term;
  sp: term Mhs.t;
}

let w_true = { wp = t_true; sp = Mhs.empty }

let w_and w1 w2 = {
  wp = t_and_simp w1.wp w2.wp;
  sp = Mhs.union (fun _ f1 f2 -> Some (t_or_simp f1 f2)) w1.sp w2.sp
}

let rec w_and_l = function
  | [] -> w_true | [w] -> w
  | w::wl -> w_and w (w_and_l wl)

let w_and_asym f w = {
  wp = t_and_asym_simp f w.wp;
  sp = Mhs.map (t_and_simp f) w.sp;
}

let w_implies f w = {
  wp = t_implies_simp f w.wp;
  sp = Mhs.map (t_and_simp f) w.sp;
}

let w_forall vl w = {
  wp = t_forall_close_simp vl [] w.wp;
  sp = Mhs.map (t_exists_close_simp vl []) w.sp
}

let rec substantial pp dd = function
  | Elam (_,e) | Eset (e,_) | Ecut (_,e) -> substantial pp dd e
  | Edef (e,_,_) when not pp -> substantial pp dd e
  | Ebox _ when not dd -> false
  | Ewox _ when not pp -> false
  | Eany -> false
  | _ -> pp || dd

let substantial pp dd gl lc e =
  (gl || not (Shs.is_empty lc)) && substantial pp dd e

type binding =
  | Bt of ty
  | Bv of term
  | Br of term * vsymbol
  | Bc of term Mvs.t * callable * bool

and callable = bool -> term Mvs.t -> binding list -> wpsp

let t_inst = ty_inst
let v_inst = t_ty_subst
let r_inst iv r = Mvs.find r iv

let lc_update gl lc pl =
  let add nc = function
    | Pt _ | Pv _ | Pr _ -> nc
    | Pc (h,_,_) -> Shs.add h nc in
  let nc = List.fold_left add Shs.empty pl in
  (if gl then Shs.empty else Shs.union lc nc), nc

let rec consume it iv ih pl bl kk =
  let init = it,iv,ih,[],[],Mvs.empty in
  let eat (it,iv,ih,zl,hl,mr) p b = match p,b with
    | Pt u, Bt t -> Mtv.add u t it, iv, ih, zl, hl, mr
    | Pv v, Bv s -> it, Mvs.add v s iv, ih, zl, hl, mr
    | Pr v, Br (s,r) -> it, Mvs.add v s iv, ih,zl,hl, Mvs.add v r mr
    | Pc ({hs_name = {id_string = s}} as h,wr,pl), Bc (ir,kk,sub) ->
        let link up p = Mvs.add (Mvs.find_def p p mr) p up in
        let up = List.fold_left link Mvs.empty wr in
        let set iv = Mvs.map (r_inst iv) up in
        let kk sf iv bl = kk sf (Mvs.set_union (set iv) ir) bl in
        if sub && List.for_all (function Pv _ | Pr _ -> true
          | Pt _ | Pc _ -> false) pl && (s <> "" && s.[0] = '_')
        then let kk, zl, hl = factorize it zl hl h wr pl kk in
             it, iv, Mhs.add h kk ih, zl, hl, mr
        else it, iv, Mhs.add h kk ih, zl, hl, mr
    | _ -> assert false in
  let it,iv,ih,zl,hl,_ = List.fold_left2 eat init pl bl in
  let w = kk it iv ih in
  let wl = List.map (fun (h,kk,zm,bl) ->
    let sp = Mhs.find_def t_false h w.sp in
    (* if is_false sp then w_true else *)
    w_implies sp (kk true zm bl)) hl in
  let drop s (h,_,_,_) = Mhs.remove h s in
  let w = { w with sp = List.fold_left drop w.sp hl } in
  w_forall (List.rev zl) (w_and_l (w :: List.rev wl))

and factorize it zl hl h wr pl kk =
  let hc = create_hsymbol (id_clone h.hs_name) in
  let dup v = create_vsymbol (id_clone v.vs_name) (t_inst it v.vs_ty) in
  let dup (zl,zm) v = let z = dup v in z::zl, Mvs.add v (t_var z) zm in
  let zl,zm = List.fold_left (fun acc -> function Pt _ | Pc _ -> assert false
    | Pv v | Pr v -> dup acc v) (List.fold_left dup (zl, Mvs.empty) wr) pl in
  let zk sf iv bl = if not sf then w_true else
    consume Mtv.empty iv Mhs.empty pl bl (fun _ iv _ ->
      let link v z f = t_and_simp (t_equ z (r_inst iv v)) f in
      let sp = Mhs.singleton hc (Mvs.fold_right link zm t_true) in
      { wp = t_true; sp = sp }) in
  let bl = List.map (function Pt _ | Pc _ -> assert false
    | Pr v -> Br (Mvs.find v zm,v) | Pv v -> Bv (Mvs.find v zm)) pl in
  zk, zl, (hc,kk,zm,bl)::hl

let rec havoc it iv ih gl wr pl kk =
  let on_write (iv,vl) p =
    let q = Mvs.find p iv in
    let id = id_clone (match q.t_node with
      | Tvar v -> v | _ -> p).vs_name in
    let r = create_vsymbol id (t_type q) in
    Mvs.add p (t_var r) iv, r::vl in
  let on_param (it,iv,ih,vl) = function
    | Pt u ->
        let v = create_tvsymbol (id_clone u.tv_name) in
        Mtv.add u (ty_var v) it, iv, ih, vl
    | Pv v | Pr v ->
        let ty = t_inst it v.vs_ty in
        let u = create_vsymbol (id_clone v.vs_name) ty in
        it, Mvs.add v (t_var u) iv, ih, u::vl
    | Pc (h,_,pl) ->
        it, iv, Mhs.add h (undef it gl pl) ih, vl in
  let iv,vl = List.fold_left on_write (iv,[]) wr in
  let it,iv,ih,vl = List.fold_left on_param (it,iv,ih,vl) pl in
  w_forall (List.rev vl) (kk it iv ih)

and undef it gl pl sf ir bl =
(*   if sf && gl then { wp = t_false; sp = Mhs.empty } else *)
  w_and { wp = if sf && gl then t_false else t_true ; sp = Mhs.empty } (
  consume it ir Mhs.empty pl bl (fun it _ ih ->
    w_and_l (List.filter_map (function
      | Pt _ | Pv _ | Pr _ -> None
      | Pc (h,wr,pl) ->
          let kk = Mhs.find h ih in
          Some (havoc it ir ih (sf && gl) wr pl (fun it iv ih ->
            let bl = List.map (function
              | Pt u -> Bt (Mtv.find u it)
              | Pv v -> Bv (r_inst iv v)
              | Pr r -> Br (r_inst iv r, r)
              | Pc (h,_,_) -> Bc (iv, Mhs.find h ih, false)) pl in
            kk true iv bl))) pl)))

let rec vc pp dd it iv ih gl lc e bl = match e with
  | Esym h -> Mhs.find h ih (pp && (gl || Shs.mem h lc)) iv bl
  | Eapp (e, At t) -> vc pp dd it iv ih gl lc e (Bt (t_inst it t)::bl)
  | Eapp (e, Av s) -> vc pp dd it iv ih gl lc e (Bv (v_inst it iv s)::bl)
  | Eapp (e, Ar r) -> vc pp dd it iv ih gl lc e (Br (r_inst iv r, r)::bl)
  | Eapp (e, Ac d) ->
      let kk sf iv bl =
        vc pp dd it iv ih (sf && gl) (if sf then lc else Shs.empty) d bl in
      vc pp dd it iv ih gl lc e (Bc (iv, kk, substantial pp dd gl lc d)::bl)
  | Elam (pl,e) ->
      let lc,nc = lc_update gl lc pl in
      consume it iv ih pl bl (fun it iv ih ->
        w_and (vc pp dd it iv ih gl lc e [])
              (vc (not pp) (not dd) it iv ih false nc e []))
  | Edef (e,flat,dfl) -> assert (bl = []);
      let pl = List.map (fun (h,w,pl,_) -> Pc (h,w,pl)) dfl in
      let nc,_ = lc_update gl lc pl in
      let lc = if flat then lc else nc in
      let spec ih (_,_,pl,d) = let lc,nc = lc_update gl lc pl in
        let kk sf iv bl = consume it iv ih pl bl (fun it iv ih ->
          vc true false it iv ih (sf && gl) (if sf then lc else nc) d []) in
        Bc (iv, kk, substantial true false gl lc d) in
      let impl ih (_,wr,pl,d) = let lc,_ = lc_update gl lc pl in
        let kk it iv ih = vc false pp it iv ih gl lc d [] in
        havoc it iv ih gl wr pl kk in
      havoc it iv ih gl [] (if flat then [] else pl) (fun it iv ih ->
        let bl = List.map (spec ih) dfl in
        w_and_l (consume it iv ih pl bl (fun it iv ih ->
            w_and_l (vc pp dd it iv ih gl nc e [] ::
              if flat then [] else List.map (impl ih) dfl))
           :: if flat then List.map (impl ih) dfl else []))
  | Eset (e,vtl) -> assert (bl = []);
      let set m (v,s) = Mvs.add v (v_inst it iv s) m in
      vc pp dd it (List.fold_left set iv vtl) ih gl lc e bl
  | Ecut (f,e) -> assert (bl = []);
      (if pp && gl then w_and_asym else w_implies)
        (v_inst it iv f) (vc pp dd it iv ih gl lc e bl)
  | Ebox e -> assert (bl = []); vc dd dd it iv ih gl lc e bl
  | Ewox e -> assert (bl = []); vc pp pp it iv ih gl lc e bl
  | Eany   -> assert (bl = []); w_true

let vc e = (vc true true Mtv.empty Mvs.empty Mhs.empty true Shs.empty e []).wp

(*
let eta h pl =
  let apply d p = Eapp (d, match p with
    | Pt u -> At (ty_var u)
    | Pv v -> Av (t_var v)
    | Pr r -> Ar r
    | Pc (g,_,_) -> Ac (Esym g)) in
  List.fold_left apply (Esym h) pl

type context = {
  c_tv : ty Mtv.t;
  c_vs : term Mvs.t;
  c_hs : closure Mhs.t;
  c_lc : Shs.t;
  c_gl : bool;
}

and closure = (* Co for outcomes (= lambdas), Cd for definitions *)
  | Co of bool * bool * context * vsymbol Mvs.t *              expr
  | Cd of bool * bool * context * vsymbol Mvs.t * param list * expr
  | Cz of               hsymbol *    term Mvs.t * param list

type binding =
  | Bt of ty
  | Bv of term
  | Br of term * vsymbol
  | Bc of bool * bool * context * expr

let c_empty = {
  c_tv = Mtv.empty;
  c_vs = Mvs.empty;
  c_hs = Mhs.empty;
  c_lc = Shs.empty;
  c_gl = true;
}

let t_inst c t = ty_inst c.c_tv t
let v_inst c t = t_ty_subst c.c_tv c.c_vs t
let r_inst c r = t_ty_subst c.c_tv c.c_vs (t_var r)

let c_add_t c u t = { c with c_tv = Mtv.add u t c.c_tv }
let c_add_v c v t = { c with c_vs = Mvs.add v t c.c_vs }

let c_add_h out (c,zl,hl,pm) h pp dd cc wr pl e =
  let to_merge = (let s = h.hs_name.id_string in s <> "" && s.[0] = '_') &&
    List.for_all (function Pv _ | Pr _ -> true | Pt _ | Pc _ -> false) pl &&
    (cc.c_gl || not (Shs.is_empty cc.c_lc)) && substantial pp dd e in
  let update up p = Mvs.add (Mvs.find_def p p pm) p up in
  let up = List.fold_left update Mvs.empty wr in
  let ce,zl,hl = if to_merge then
    let hc = create_hsymbol (id_clone h.hs_name) in
    let dup v = create_vsymbol (id_clone v.vs_name) (t_inst c v.vs_ty) in
    let dup (zl,zm) v = let z = dup v in z::zl, Mvs.add v (t_var z) zm in
    let zl,zm = List.fold_left (fun acc -> function Pt _ | Pc _ -> assert false
      | Pv v | Pr v -> dup acc v) (List.fold_left dup (zl, Mvs.empty) wr) pl in
    let bl = if out then List.map (function Pt _ | Pc _ -> assert false
      | Pr v -> Br (Mvs.find v zm,v) | Pv v -> Bv (Mvs.find v zm)) pl else [] in
    let up = if out then Mvs.map (fun p -> Mvs.find p zm) up else zm in
    let cc = { cc with c_vs = Mvs.set_union up cc.c_vs } in
    Cz (hc,zm,pl), zl, (hc,pp,dd,cc,bl,e)::hl
  else if out then Co (pp,dd,cc,up,e), zl, hl
              else Cd (pp,dd,cc,up,pl,e), zl, hl in
  let lc = if c.c_gl then Shs.empty else Shs.add h c.c_lc in
  { c with c_hs = Mhs.add h ce c.c_hs; c_lc = lc },zl,hl,pm

let consume c pl bl =
  let eat (c,zl,hl,m as acc) p b = match p, b with
    | Pt u, Bt t -> c_add_t c u t, zl, hl, m
    | Pv v, Bv t -> c_add_v c v t, zl, hl, m
    | Pr p, Br (q,r) -> c_add_v c p q, zl, hl, Mvs.add p r m
    | Pc (h,wr,pl), Bc (pp,dd,cc,e) -> c_add_h true acc h pp dd cc wr pl e
    | _ -> assert false in
  List.fold_left2 eat (c,[],[],Mvs.empty) pl bl

let rec vc pp dd c bl = function
  | Esym h ->
      let safe = pp && (c.c_gl || Shs.mem h c.c_lc) in
      let update cc wr = { cc with
        c_vs = Mvs.set_union (Mvs.map (r_inst c) wr) cc.c_vs;
        c_lc = if safe then cc.c_lc else Shs.empty;
        c_gl = safe && cc.c_gl } in
      (match Mhs.find h c.c_hs with
      | Co (pp,dd,cc,wr,d) ->
          vc pp dd (update cc wr) bl d
      | Cd (pp,dd,cc,wr,pl,d) ->
          let cc,zl,hl,_ = consume (update cc wr) pl bl in
          discharge (vc pp dd cc [] d) zl hl
      | Cz (h,zm,pl) when safe ->
          let c,_,_,_ = consume c pl bl in
          let add v z f = t_and_simp (t_equ z (r_inst c v)) f in
          let sp = Mvs.fold_right add zm t_true in
          { wp = t_true; sp = Mhs.singleton h sp }
      | Cz _ -> w_true)
  | Eapp (e,a) ->
      let b = match a with
        | At t -> Bt (t_inst c t)
        | Av t -> Bv (v_inst c t)
        | Ar r -> Br (r_inst c r,r)
        | Ac d -> Bc (pp,dd,c,d) in
      vc pp dd c (b::bl) e
  | Elam (pl,e) ->
      let c,zl,hl,_ = consume c pl bl in
      let lc = List.fold_left (fun s -> function
        | Pc (h,_,_) -> Shs.add h s
        | Pt _ | Pv _ | Pr _ -> s) Shs.empty pl in
      let cw = { c with c_lc = lc; c_gl = false } in
      let w = w_and (vc pp dd c [] e) (vc (not pp) (not dd) cw [] e) in
      discharge w zl hl
  | Edef (e,flat,dfl) -> assert (bl = []);
      let cr = if flat then c else
        let pc_of_def (h,wr,pl,_) = Pc (h,wr,pl) in
        fst (havoc c [] (List.map pc_of_def dfl)) in
      let spec c (h,w,l,d) = c_add_h false c h true false cr w l d in
      let cl,zl,hl,_ = List.fold_left spec (c,[],[],Mvs.empty) dfl in
      let impl (_,wr,pl,d) =
        let c,vl = havoc (if flat then c else cl) wr pl in
        w_forall vl (vc false pp c [] d) in
      let wl = vc pp dd cl [] e :: List.map impl dfl in
      discharge (w_and_l wl) zl hl
  | Eset (e,vtl) -> assert (bl = []);
      let set cl (v,t) = c_add_v cl v (v_inst c t) in
      vc pp dd (List.fold_left set c vtl) [] e
  | Ecut (f,e) -> assert (bl = []);
      (if pp && c.c_gl then w_and_asym else w_implies)
        (v_inst c f) (vc pp dd c [] e)
  | Ebox e -> assert (bl = []); vc dd dd c [] e
  | Ewox e -> assert (bl = []); vc pp pp c [] e
  | Eany   -> assert (bl = []); w_true

and discharge w zl hl =
  let wl = List.map (fun (h,pp,dd,c,bl,e) ->
    let sp = Mhs.find_def t_false h w.sp in
    (* if is_false sp then w_true else *)
    w_implies sp (vc pp dd c bl e)) hl in
  let drop s (h,_,_,_,_,_) = Mhs.remove h s in
  let w = { w with sp = List.fold_left drop w.sp hl } in
  w_forall (List.rev zl) (w_and_l (w :: List.rev wl))

and havoc c wr pl =
  let on_write (vl,c) p =
    let q = Mvs.find p c.c_vs in
    let id = id_clone (match q.t_node with
      | Tvar v -> v | _ -> p).vs_name in
    let r = create_vsymbol id (t_type q) in
    r::vl, c_add_v c p (t_var r) in
  let on_param (vl,c) = function
    | Pt u ->
        let v = create_tvsymbol (id_clone u.tv_name) in
        vl, c_add_t c u (ty_var v)
    | Pv v | Pr v ->
        let ty = t_inst c v.vs_ty in
        let u = create_vsymbol (id_clone v.vs_name) ty in
        u::vl, c_add_v c v (t_var u)
    | Pc (h,wr,pl) ->
        let d = Ecut (t_false, Eany) in
        let dl = List.filter_map (function
          | Pc (h,wr,pl) -> Some (h,wr,pl,Ebox (eta h pl))
          | Pt _ | Pv _ | Pr _ -> None) pl in
        let d = if dl = [] then d else Edef (d,true,dl) in
        let c,_,_,_ = c_add_h false (c,[],[],Mvs.empty)
                              h true true c wr pl d in
        vl,c in
  let vl,c = List.fold_left on_write ([],c) wr in
  let vl,c = List.fold_left on_param (vl,c) pl in
  c, List.rev vl

let vc e = (vc true true c_empty [] e).wp
*)

(*
let (!) h = Esym h

let (--) e t = Eapp (e, At t)
let (-+) e t = Eapp (e, Av t)
let (-&) e r = Eapp (e, Ar r)
let (-* ) e d = Eapp (e, Ac d)

let (<>) e vtl         = Eset (e,vtl)
let (>>) e (h,wr,pl,d) = Edef (e,true, [h,wr,pl,d])
let (<<) e (h,wr,pl,d) = Edef (e,false,[h,wr,pl,d])

let def h wr pl d = (h,wr,pl,d)
let lam pl d = Elam (pl,d)

let cut f d = Ecut (f,d)

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
let hs_ret_ = create_hsymbol (id_fresh "_ret")

let vs_ii = create_vsymbol (id_fresh "i") ty_int
let vs_ji = create_vsymbol (id_fresh "j") ty_int
(*
let vs_ki = create_vsymbol (id_fresh "k") ty_int
let vs_li = create_vsymbol (id_fresh "l") ty_int
let vs_mi = create_vsymbol (id_fresh "m") ty_int
*)
let vs_pi = create_vsymbol (id_fresh "p") ty_int
let vs_qi = create_vsymbol (id_fresh "q") ty_int

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

let _expr1 =
  !hs_alloc -- ty_int -+ t_nat_const 1 -* lam [Pr vs_pi] (
    !hs_loop -- ty_int -+ t_var vs_pi -* !hs_out -+
                              t_nat_const 3 -+ t_nat_const 0 -+ t_nat_const 5
    << def hs_loop [vs_pi] [Pt tv_a; Pv vs_ia; Pc (hs_ret,[vs_pi],[Pv vs_ja]);
                                                Pv vs_ka; Pv vs_la; Pv vs_ma]
          (cut (t_and (t_neq (t_var vs_ia) (t_var vs_ka))
                   (t_neq (t_var vs_pi) (t_nat_const 9)))
          (Ebox (!hs_if -+ (t_if (t_equ (t_var vs_ia) (t_var vs_la))
                                t_bool_true t_bool_false) -*
             lam [] (!hs_assign -- ty_int -& vs_pi -+ t_nat_const 2 -*
                lam [] (cut (t_neq (t_var vs_qi) (t_var vs_pi))
                  (!hs_loop -- ty_var tv_a -+ t_var vs_ia -* !hs_ret_
                    -+ t_var vs_la -+ t_var vs_ma -+ t_var vs_ka))
                <> [vs_qi, t_var vs_pi]) -*
             lam [] (!hs_ret_ -+ t_var vs_ia)))
        >> def hs_ret_ [vs_pi] [Pv vs_ja]
          (cut (t_and (t_equ (t_var vs_ma) (t_var vs_ja))
                       (t_equ (t_nat_const 55) (t_var vs_pi)))
                                   (Ebox (!hs_ret -+ t_var vs_ja))))
    >> def hs_out [vs_pi] [Pv vs_ii]
      (cut (t_and (t_equ (t_var vs_ii) (t_nat_const 42))
                   (t_equ (t_var vs_pi) (t_nat_const 37))) (Ebox !hs_halt)))
  >> def hs_assign [] [Pt tv_c; Pr vs_uc; Pv vs_vc; Pc (hs_ret,[vs_uc],[])]
      (Eany >> def hs_ret [vs_uc] [] (cut (t_equ (t_var vs_uc) (t_var vs_vc))
                                              (Ebox (!hs_ret))))
  >> def hs_alloc [] [Pt tv_c; Pv vs_vc; Pc (hs_ret,[],[Pr vs_uc])]
      (Eany >> def hs_ret [] [Pr vs_uc] (cut (t_equ (t_var vs_uc) (t_var vs_vc))
                                              (Ebox (!hs_ret -& vs_uc))))
  >> def hs_if [] [Pv vs_bb; Pc (hs_then,[],[]); Pc (hs_else,[],[])]
      (Eany >> def hs_then [] [] (cut (t_equ (t_var vs_bb) t_bool_true) (Ebox !hs_then))
            >> def hs_else [] [] (cut (t_equ (t_var vs_bb) t_bool_false) (Ebox !hs_else)))
  >> def hs_fail [] [] (cut t_false Eany)
  >> def hs_halt [] [] (Ewox Eany)

let _expr2 =
  !hs_alloc -- ty_int -+ t_nat_const 1 -* lam [Pr vs_qi] (
    !hs_loop -& vs_qi -- ty_int -+ t_var vs_qi -*
                          lam [Pv vs_ji] (!hs_out -& vs_qi -+ t_var vs_ji) -+
                              t_nat_const 3 -+ t_nat_const 0 -+ t_nat_const 5)
  << def hs_loop [] [Pr vs_pi; Pt tv_a; Pv vs_ia; Pc (hs_ret,[vs_pi],[Pv vs_ja]);
                                              Pv vs_ka; Pv vs_la; Pv vs_ma]
        (cut (t_and (t_neq (t_var vs_ia) (t_var vs_ka))
                  (t_neq (t_var vs_pi) (t_nat_const 9)))
        (Ebox (!hs_if -+ (t_if (t_equ (t_var vs_ia) (t_var vs_la))
                              t_bool_true t_bool_false) -*
            lam [] (!hs_assign -- ty_int -& vs_pi -+ t_nat_const 2 -*
              lam [] (cut (t_neq (t_var vs_qi) (t_var vs_pi))
                (!hs_loop -& vs_pi -- ty_var tv_a -+ t_var vs_ia -* !hs_ret_
                  -+ t_var vs_la -+ t_var vs_ma -+ t_var vs_ka))
              <> [vs_qi, t_var vs_pi]) -*
            lam [] (!hs_ret_ -+ t_var vs_ia)))
      >> def hs_ret_ [vs_pi] [Pv vs_ja]
        (cut (t_and (t_equ (t_var vs_ma) (t_var vs_ja))
                      (t_equ (t_nat_const 55) (t_var vs_pi)))
                                  (Ebox (!hs_ret -+ t_var vs_ja))))
  >> def hs_out [] [Pr vs_pi; Pv vs_ii]
      (cut (t_and (t_equ (t_var vs_ii) (t_nat_const 42))
                   (t_equ (t_var vs_pi) (t_nat_const 37))) (Ebox !hs_halt))
  >> def hs_assign [] [Pt tv_c; Pr vs_uc; Pv vs_vc; Pc (hs_ret,[vs_uc],[])]
      (Eany >> def hs_ret [vs_uc] [] (cut (t_equ (t_var vs_uc) (t_var vs_vc))
                                              (Ebox (!hs_ret))))
  >> def hs_alloc [] [Pt tv_c; Pv vs_vc; Pc (hs_ret,[],[Pr vs_uc])]
      (Eany >> def hs_ret [] [Pr vs_uc] (cut (t_equ (t_var vs_uc) (t_var vs_vc))
                                              (Ebox (!hs_ret -& vs_uc))))
  >> def hs_if [] [Pv vs_bb; Pc (hs_then,[],[]); Pc (hs_else,[],[])]
      (Eany >> def hs_then [] [] (cut (t_equ (t_var vs_bb) t_bool_true) (Ebox !hs_then))
            >> def hs_else [] [] (cut (t_equ (t_var vs_bb) t_bool_false) (Ebox !hs_else)))
  >> def hs_fail [] [] (cut t_false Eany)
  >> def hs_halt [] [] (Ewox Eany)

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
