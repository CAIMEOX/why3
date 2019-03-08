open Why3
open Ident
open Term
open Decl
open Theory
open Task
open Generic_arg_trans_utils
open Format

type ident = Ident.ident

type binop = CTand | CTor | CTiff | CTimplies
type cterm = CTapp of ident
           | CTbinop of binop * cterm * cterm


type ctask = {hyp : cterm Mid.t; concl : cterm Mid.t}
let mct mid1 mid2 = {hyp = mid1; concl = mid2}

let map_ctask (f : bool -> ident -> cterm -> cterm) {hyp = hyp; concl = concl} =
  let hyp = Mid.mapi (f false) hyp in
  let concl = Mid.mapi (f true) concl in
  {hyp = hyp; concl = concl}

type dir = Left | Right
type path = dir list
type certif = Skip
            | Axiom of ident
            | Split of certif * certif
            | Dir of dir * certif
            | Intro of ident * certif
            | Rewrite of bool * ident * ident * path * certif list


type ctrans = task -> task list * certif

let rec cterm_equal t1 t2 =
  match t1, t2 with
  | CTapp i1, CTapp i2 -> Ident.id_equal i1 i2
  | CTbinop (op1, tl1, tr1), CTbinop (op2, tl2, tr2) ->
      op1 = op2 && cterm_equal tl1 tl2 && cterm_equal tr1 tr2
  | _ -> false

let ctask_equal {hyp = h1; concl = c1} {hyp = h2; concl = c2} =
  Mid.equal cterm_equal h1 h2 && Mid.equal cterm_equal c1 c2


(* For debugging purposes *)
let rec print_certif where cert =
  let oc = open_out where in
  let fmt = formatter_of_out_channel oc in
  fprintf fmt "%a@." prc cert;
  close_out oc
and prc (fmt : formatter) = function
  | Skip -> fprintf fmt "Skip"
  | Axiom i -> fprintf fmt "Axiom %a" pri i
  | Split (c1, c2) -> fprintf fmt "Split @[(%a,@ %a)@]" prc c1 prc c2
  | Dir (d, c) -> fprintf fmt "Dir @[(%a,@ %a)@]" prd d prc c
  | Intro (i, c) -> fprintf fmt "Intro @[(%a,@ %a)@]" pri i prc c
  | Rewrite (rev, rh, th, p, lc) ->
      fprintf fmt "Rewrite @[(%b,@ %a,@ %a,@ %a,@ %a)@]"
        rev pri rh pri th (prle prd) p (prle prc) lc
and pri fmt i =
  fprintf fmt "%s" Ident.(id_clone i |> preid_name)
and prd fmt = function
  | Left -> fprintf fmt "Left"
  | Right -> fprintf fmt "Right"
and prle : type a. (formatter -> a -> unit) -> formatter -> a list -> unit = fun pre fmt le ->
  let prl le = pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "; ") pre le in
  fprintf fmt "[%a]" prl le





(** Translating Why3 tasks to simplified certificate tasks *)

let rec translate_term (t : term) : cterm =
  match t.t_node with
  | Tapp (ls, []) -> CTapp ls.ls_name
  | Tbinop (Tand, t1, t2) -> CTbinop (CTand, translate_term t1, translate_term t2)
  | Tbinop (Tor , t1, t2) -> CTbinop (CTor , translate_term t1, translate_term t2)
  | Tbinop (Tiff, t1, t2) -> CTbinop (CTiff, translate_term t1, translate_term t2)
  | Tbinop (Timplies, t1, t2) -> CTbinop (CTimplies, translate_term t1, translate_term t2)
  | _ -> invalid_arg "Cert_syntax.translate_term"

let translate_decl (d : decl) : ctask =
  match d.d_node with
  | Dprop (Pgoal, pr, f) ->
      let concl = Mid.singleton pr.pr_name (translate_term f) in
      mct Mid.empty concl
  | Dprop (_, pr, f) ->
      let hyp = Mid.singleton pr.pr_name (translate_term f) in
      mct hyp Mid.empty
  | _ -> mct Mid.empty Mid.empty

let translate_tdecl (td : tdecl) : ctask =
  match td.td_node with
  | Decl d -> translate_decl d
  | _ -> mct Mid.empty Mid.empty

let union_ctask {hyp = h1; concl = c1} {hyp = h2; concl = c2} =
  mct (Mid.set_union h1 h2) (Mid.set_union c1 c2)

let rec translate_task_acc acc = function
  | Some {task_decl = d; task_prev = p} ->
      let new_acc = union_ctask acc (translate_tdecl d) in
      translate_task_acc new_acc p
  | None -> acc

let translate_task t =
  translate_task_acc (mct Mid.empty Mid.empty) t

(** Using ctasks and certificates *)

(* check_certif replays the certificate on a ctask *)
exception Certif_verification_failed of string
let verif_failed s = raise (Certif_verification_failed s)

(* Ensures the goal has exactly one cterm *)
let normalized_goal concl : ident * cterm =
  let fold_concl g_opt id ng = match g_opt with
        | None -> Some (id, ng)
        | Some _ -> verif_failed "Multiple goals" in
  match Mid.fold_left fold_concl None concl with
  | None -> verif_failed "No goal"
  | Some t -> t

let rec check_rewrite_term tl tr t p =
  match p, t with
  | [], t when cterm_equal t tl -> tr
  | Left::prest, CTbinop (op, t1, t2) ->
      let nt1 = check_rewrite_term tl tr t1 prest in
      CTbinop (op, nt1, t2)
  | Right::prest, CTbinop (op, t1, t2) ->
      let nt2 = check_rewrite_term tl tr t2 prest in
      CTbinop (op, t1, nt2)
  | _ -> verif_failed "Can't follow the rewrite path"

let check_rewrite cta rev rh th p : ctask list =
  let rec introduce acc = function
    | CTbinop (CTimplies, t1, t2) -> introduce (t1::acc) t2
    | t -> acc, t in
  let lp, tl, tr = match introduce [] (Mid.find rh cta.hyp) with
      | lp, CTbinop (CTiff, t1, t2) -> if rev then lp, t1, t2 else lp, t2, t1
      | _ -> verif_failed "Can't find the hypothesis used to rewrite" in
  let rewrite_decl _ id te =
    if id_equal id th
    then check_rewrite_term tl tr te p
    else te in
  [map_ctask rewrite_decl cta]

let rec check_certif ({hyp = hyp; concl = concl} as cta) (cert : certif) : ctask list =
  match cert with
    | Skip -> [cta]
    | Axiom id ->
        let found = Mid.find_opt id hyp in
        let _, teg = normalized_goal concl in
        begin match found with
        | Some tef when tef = teg -> []
        | _ -> verif_failed "No such assumption" end
    | Split (c1, c2) ->
        let idg, teg = normalized_goal concl in
        begin match teg with
        | CTbinop (CTand, t1, t2) ->
            let cta1 = {cta with concl = Mid.singleton idg t1} in
            let cta2 = {cta with concl = Mid.singleton idg t2} in
            check_certif cta1 c1 @ check_certif cta2 c2
        | CTbinop (CTiff, t1, t2) ->
            let cta1 = {cta with concl = Mid.singleton idg (CTbinop (CTimplies, t1, t2))} in
            let cta2 = {cta with concl = Mid.singleton idg (CTbinop (CTimplies, t2, t1))} in
            check_certif cta1 c1 @ check_certif cta2 c2
        | _ -> verif_failed "Goal is not splittable" end
    | Dir (d, c) ->
        let idg, teg = normalized_goal concl in
        begin match teg, d with
        | CTbinop(CTor, t, _), Left | CTbinop (CTor, _, t), Right ->
            let cta = {cta with concl = Mid.singleton idg t} in
            check_certif cta c
        | _ -> verif_failed "Can't follow a direction" end
    | Intro (i, c) ->
        let idg, teg = normalized_goal concl in
        begin match teg with
        | CTbinop (CTimplies, f1, f2) ->
            let cta = {hyp = Mid.add i f1 hyp; concl = Mid.singleton idg f2 } in
            check_certif cta c
        | _ -> verif_failed "Nothing to introduce" end
    | Rewrite (rev, rh, th, p, lc) ->
        let lcta = check_rewrite cta rev rh th p in
        List.map2 check_certif lcta lc |> List.concat

(* Creates a certified transformation from a transformation with certificate *)
let checker_ctrans ctr task =
  try let ltask, cert = ctr task in
      print_certif "/tmp/certif.log" cert;
      let ctask = translate_task task in
      let lctask = check_certif ctask cert in
      if Lists.equal ctask_equal lctask (List.map translate_task ltask)
      then ltask
      else verif_failed "Replaying certif gives different result"
  with e -> raise (Trans.TransFailure ("Cert_syntax.checker_ctrans", e))

(* Generalize ctrans on (task list * certif) *)
let ctrans_gen (ctr : ctrans) (ts, c) =
  let rec fill acc c ts = match c with
      | Skip -> begin match ts with
                | [] -> assert false
                | t::ts -> let lt, ct = ctr t in
                           lt :: acc, ct, ts end
      | Axiom _ -> [], c, ts
      | Split (c1, c2) -> let acc, c1, ts = fill acc c1 ts in
                          let acc, c2, ts = fill acc c2 ts in
                          acc, Split (c1, c2), ts
      | Dir (d, c) -> let acc, c, ts = fill acc c ts in
                      acc, Dir (d, c), ts
      | Intro (i, c) -> let acc, c, ts = fill acc c ts in
                        acc, Intro (i, c), ts
      | Rewrite (rev, t1, t2, p, lc) ->
          let acc, lc, ts = List.fold_left (fun (acc, lc, ts) nc ->
                                let acc, c, ts = fill acc nc ts in
                                (acc, c::lc, ts)) (acc, [], ts) lc in
          acc, Rewrite (rev, t1, t2, p, List.rev lc), ts
  in
  let acc, c, ts = fill [] c ts in
  assert (ts = []);
  let rev_concat l1 l2 = List.fold_left (fun acc l -> l @ acc) l2 l1 in
  rev_concat acc [], c

let rec nocuts = function
  | Skip -> false
  | Axiom _ -> true
  | Split (c1, c2) -> nocuts c1 && nocuts c2
  | Dir (_, c)
  | Intro (_, c) -> nocuts c
  | Rewrite (_, _, _, _, lc) -> List.for_all nocuts lc

(** Primitive transformations with certificate *)

(* Identity transformation with certificate *)
let id task = [task], Skip

(* Assumption with certificate *)
let assumption_decl g (d : decl) =
  match d.d_node with
  | Dprop (_, pr, f) -> if t_equal_nt_na g f
                        then Some pr.pr_name
                        else None
  | _ -> None

let assumption_tdecl g (td : tdecl) =
  match td.td_node with
  | Decl d -> assumption_decl g d
  | _ -> None

let rec assumption_ctxt g = function
  | Some {task_decl = d; task_prev = p} ->
      begin match assumption_tdecl g d with
      | Some h -> h
      | None -> assumption_ctxt g p end
  | None -> raise Not_found

let assumption t =
  let g = try task_goal_fmla t
          with GoalNotFound -> invalid_arg "Cert_syntax.assumption" in
  let _, t' = task_separate_goal t in
  try let h = assumption_ctxt g t' in
      [], Axiom h
  with Not_found -> [t], Skip

(* Split with certificate *)
let split t =
  let pr, g = try task_goal t, task_goal_fmla t
              with GoalNotFound -> invalid_arg "Cert_syntax.split" in
  let _, c = task_separate_goal t in
  let splitted = match g.t_node with
    | Tbinop (Tand, f1, f2) -> Some (f1, f2)
    | Tbinop (Tiff, f1, f2) ->
        let direct = t_implies f1 f2 in
        let indirect = t_implies f2 f1 in
        Some (direct, indirect)
    | _ -> None in
  match splitted with
    | Some (f1, f2) ->
        let tf1 = add_decl c (create_prop_decl Pgoal pr f1) in
        let tf2 = add_decl c (create_prop_decl Pgoal pr f2) in
        [tf1;tf2], Split (Skip, Skip)
    | None -> [t], Skip

(* Intro with certificate *)
let intro t =
  let i = Decl.create_prsymbol (Ident.id_fresh "i") in
  let pr, g = try task_goal t, task_goal_fmla t
              with GoalNotFound -> invalid_arg "Cert_syntax.split" in
  let _, c = task_separate_goal t in
  match g.t_node with
  | Tbinop (Timplies, f1, f2) ->
      let decl1 = create_prop_decl Paxiom i f1 in
      let tf1 = add_decl c decl1 in
      let tf2 = add_decl tf1 (create_prop_decl Pgoal pr f2) in
      [tf2], Intro (i.pr_name, Skip)
  | _ -> [t], Skip

(* Direction with certificate *)
let dir d t =
  let pr, g = try task_goal t, task_goal_fmla t
              with GoalNotFound -> invalid_arg "Cert_syntax.dir" in
  let _, c = task_separate_goal t in
  match g.t_node, d with
  | Tbinop (Tor, f, _), Left | Tbinop (Tor, _, f), Right ->
      let tf = add_decl c (create_prop_decl Pgoal pr f) in
      [tf], Dir (d, Skip)
  | _ -> [t], Skip

(* Rewrite with certificate *)
let rec rewrite_in_term tl tr t : (term * path) option =
  if t_equal tl t
  then Some (tr, [])
  else match t.t_node with
       | Tbinop (op, t1, t2) ->
           begin match rewrite_in_term tl tr t1 with
           | Some (nt1, p) -> Some (t_binary op nt1 t2, Left::p)
           | None -> match rewrite_in_term tl tr t2 with
                     | Some (nt2, p) -> Some (t_binary op t1 nt2, Right::p)
                     | None -> None end
       | _ -> None

let rec intro_premises acc t = match t.t_node with
  | Tbinop (Timplies, f1, f2) -> intro_premises (f1::acc) f2
  | _ -> acc, t

let rewrite_in rev h h1 task =
  let h = h.pr_name and h1 = h1.pr_name in
  let path = ref [] in
  let found_eq =
    (* Used to find the equality we are rewriting on *)
    (* TODO here should fold with a boolean stating if we found equality yet to
       not go through all possible hypotheses *)
    Trans.fold_decl (fun d acc ->
      match d.d_node with
      | Dprop (Paxiom, pr, t) when Ident.id_equal pr.pr_name h ->
          let lp, f = intro_premises [] t in
          let t1, t2 = (match f.t_node with
          | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
              (* Support to rewrite from the right *)
              if rev then (t1, t2) else (t2, t1)
          | Tbinop (Tiff, t1, t2) ->
              (* Support to rewrite from the right *)
              if rev then (t1, t2) else (t2, t1)
          | _ -> raise (Arg_bad_hypothesis ("rewrite", f))) in
          Some (lp, t1, t2)
      | _ -> acc)
      None
  in
  (* Return instantiated premises and the hypothesis correctly rewritten *)
  let lp_new found_eq =
    match found_eq with
    | None -> raise (Args_wrapper.Arg_error "rewrite") (* Should not happen *)
    | Some (lp, t1, t2) ->
      Trans.fold_decl (fun d acc ->
        match d.d_node with
        | Dprop (p, pr, t) when id_equal pr.pr_name h1 && (p = Pgoal || p = Paxiom)->
            let new_term, pat = match rewrite_in_term t1 t2 t with
              | Some (new_term, pat) -> new_term, pat
              | None -> failwith "Nothing to rewrite" in
            path := pat;
            Some (lp, create_prop_decl p pr new_term)
        | _ -> acc) None in
  (* Pass the premises as new goals. Replace the former toberewritten
     hypothesis to the new rewritten one *)
  let recreate_tasks lp_new =
    match lp_new with
    | None -> raise (Arg_trans "recreate_tasks")
    | Some (lp, new_decl) ->
      let trans_rewriting =
        Trans.decl (fun d -> match d.d_node with
        | Dprop (p, pr, _t) when id_equal pr.pr_name h1 && (p = Paxiom || p = Pgoal) ->
            [new_decl]
        | _ -> [d]) None in
      let list_par =
        List.map (fun e ->
            Trans.decl (fun d -> match d.d_node with
            | Dprop (Pgoal, _, _) ->
                [create_goal ~expl:"rewrite premises" (create_prsymbol (gen_ident "G")) e]
            | _ -> [d])
          None) lp in
      Trans.par (trans_rewriting :: list_par) in

  (* Composing previous functions *)
  let gen_task = Trans.apply (Trans.bind (Trans.bind found_eq lp_new) recreate_tasks) task in
  gen_task, Rewrite (rev, h, h1, !path, [Skip])

let rewrite rev h h1 task =
  let h1 = match h1 with
    | Some pr -> pr
    | None -> task_goal task in
  rewrite_in (not rev) h h1 task


(** Transformials *)

(* Compose transformations with certificate *)
let compose (tr1 : ctrans) (tr2 : ctrans) : ctrans = fun task ->
  tr1 task |> ctrans_gen tr2

(* If Then Else on transformations with certificate *)
let ite (tri : ctrans) (trt : ctrans) (tre : ctrans) : ctrans = fun task ->
  let ((lt, cert) as tri_task) = tri task in
  if not (Lists.equal task_equal lt [task] && cert = Skip)
  then ctrans_gen trt tri_task
  else ctrans_gen tre tri_task

(* Try on transformations with certificate *)
let rec try_close (lctr : ctrans list) : ctrans = fun task ->
  match lctr with
  | [] -> id task
  | h::t -> let lctask_h, cert_h = h task in
            if lctask_h = []
            then [], cert_h
            else try_close t task

(* Repeat on transformations with certificate *)
let repeat (ctr : ctrans) : ctrans = fun task ->
  let gen_task = id task in
  let gen_tr = ctrans_gen ctr in
  let rec loop gt =
    let new_gt = gen_tr gt in
    if Lists.equal task_equal (fst new_gt) (fst gt)
    then gt
    else loop new_gt in
  loop gen_task


(** Derived transformations with certificate *)

let intros = repeat intro

let rec intuition task =
  repeat (compose assumption
            (compose intro
               (compose split
                  (try_close [ite (dir Left) intuition id;
                              ite (dir Right) intuition id])))) task


(** Certified transformations *)

let assumption_trans = checker_ctrans assumption
let split_trans = checker_ctrans split
let intro_trans = checker_ctrans intro
let left_trans = checker_ctrans (dir Left)
let right_trans = checker_ctrans (dir Right)
let rewrite_trans rev rh th = checker_ctrans (rewrite rev rh th)

let intros_trans = checker_ctrans intros
let intuition_trans = checker_ctrans intuition

let () =
  Trans.register_transform_l "assumption_cert" (Trans.store assumption_trans)
    ~desc:"A certified version of coq tactic [assumption]";
  Trans.register_transform_l "split_cert" (Trans.store split_trans)
    ~desc:"A certified version of (simplified) coq tactic [split]";
  Trans.register_transform_l "intro_cert" (Trans.store intro_trans)
    ~desc:"A certified version of (simplified) coq tactic [intro]";
  Trans.register_transform_l "left_cert" (Trans.store left_trans)
    ~desc:"A certified version of coq tactic [left]";
  Trans.register_transform_l "right_cert" (Trans.store right_trans)
    ~desc:"A certified version of coq tactic [right]";
  let open Args_wrapper in
  wrap_and_register ~desc:"A certified version of transformation rewrite"
    "rewrite_cert" (Toptbool ("<-", (Tprsymbol (Topt ("in", Tprsymbol (Ttrans_l))))))
    (fun rev rh th -> Trans.store (rewrite_trans rev rh th))


let () =
  Trans.register_transform_l "intros_cert" (Trans.store intros_trans)
    ~desc:"A certified version of coq tactic [intros]";
  Trans.register_transform_l "intuition_cert" (Trans.store intuition_trans)
    ~desc:"A certified version of (simplified) coq tactic [intuition]"
