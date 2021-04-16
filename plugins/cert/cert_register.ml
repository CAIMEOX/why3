open Why3
open Ident
open Task

open Cert_syntax
open Cert_abstract
open Cert_certificates
open Cert_split
open Cert_induction
open Cert_trans_core
open Cert_rewrite
open Cert_verif_caml
open Cert_verif_lambdapi

(** Certified transformations *)

let no_dbg = None, None
let cert_dbg = Some eprcertif, None
let cta_dbg = None, Some eplcta
let all_dbg = Some eprcertif, Some eplcta

(** Get a certified transformation from a transformation with a certificate *)

let checker_ctrans
      ?env
      (debug :   (visible_cert -> unit) option *
                 (kernel_ctask -> kernel_ctask list -> unit) option )
      (* is_lp *)
      (checker : kernel_ecert -> kernel_ctask -> kernel_ctask list -> unit)
      (ctr : visible_cert ctransformation)
      (init_t : task) =
  try
    let dbg_cert, dbg_cta = debug in
    (* let t1 = Unix.times () in *)
    let res_t, certif = Trans.apply ctr init_t in
    (* let t2 = Unix.times () in *)
    Opt.iter (fun eprcertif -> eprcertif certif) dbg_cert;
    let abstract_task = abstract_task env in
    let init_ct = abstract_task init_t in
    let res_ct = List.map abstract_task res_t in
    let kernel_certif = make_kernel_cert init_ct res_t certif in
    let init_ct = abstract_terms_task init_ct in
    let res_ct = List.map abstract_terms_task res_ct in
    Opt.iter (fun eplcta -> eplcta init_ct res_ct) dbg_cta;
    checker kernel_certif init_ct res_ct;
    (* let t3 = Unix.times () in *)
    (* let syst = if is_lp then "Lambdapi" else "OCaml" in *)
    (* eprintf "@[<v>temps de la transformation : %f@ \
     *          temps de la transformation (fils) : %f@ \
     *          temps du %s-checker : %f@ \
     *          temps du %s-checker (fils): %f@ @]"
     *          (t2.Unix.tms_utime-.t1.Unix.tms_utime +. t2.Unix.tms_stime -. t1.Unix.tms_stime)
     *          (t2.Unix.tms_cutime-.t1.Unix.tms_cutime +. t2.Unix.tms_cstime -. t1.Unix.tms_cstime)
     *          syst (t3.Unix.tms_utime-.t2.Unix.tms_utime +. t3.Unix.tms_stime -. t2.Unix.tms_stime)
     *          syst (t3.Unix.tms_cutime-.t2.Unix.tms_cutime +. t3.Unix.tms_cstime -. t2.Unix.tms_cstime); *)
    forget_all ip;
    forget_all hip;
    res_t
  with Invalid_argument s -> forget_all ip;
            forget_all hip;
            Format.printf "%s" s;
            raise Not_found
     | Not_found -> raise Found



let cchecker ?env trans =
  Trans.store (checker_ctrans ?env no_dbg checker_caml trans)
let lchecker ?env trans =
  Trans.store (checker_ctrans ?env no_dbg checker_lambdapi trans)

let induction_c x bound env = cchecker ~env:env (induction x bound env)
let induction_l x bound env = lchecker ~env:env (induction x bound env)

let print_c any every where = cchecker (tprint any every where)
let assert_c t              = cchecker (cassert t)
let assumption_c            = cchecker assumption
let blast_c                 = cchecker blast
let case_c t                = cchecker (case t)
let clear_c l               = cchecker (clear l)
let contradict_c            = cchecker contradict
let destruct_all_c any every where = cchecker (destruct_all any every where)
let exfalso_c               = cchecker exfalso
let instantiate_c t what    = cchecker (inst t what)
let intro_c any every where = cchecker (intro any every where)
let intros_c                = cchecker intros
let left_c where            = cchecker (cdir false where)
(* let pose_c name t           = cchecker (pose name t) *)
let rename_c pr1            = cchecker (crename pr1)
let revert_c ls             = cchecker (revert ls)
let rewrite_c rev g where wt= cchecker (rewrite g rev wt where)
let right_c where           = cchecker (cdir true where)
let split_c any every where = cchecker (split_logic any every where)
let split_all_full_c        = cchecker split_all_full
let split_all_right_c       = cchecker split_all_right
let split_goal_full_c       = cchecker split_goal_full
let split_goal_right_c      = cchecker split_goal_right
let split_premise_full_c    = cchecker split_premise_full
let split_premise_right_c   = cchecker split_premise_right
let swap_c where            = cchecker (swap where)
let trivial_c               = cchecker trivial


let assert_l t              = lchecker (cassert t)
let assumption_l            = lchecker assumption
let blast_l                 = lchecker blast
let case_l t                = lchecker (case t)
let clear_l l               = lchecker (clear l)
let contradict_l            = lchecker contradict
let destruct_all_l any every where = lchecker (destruct_all any every where)
let exfalso_l               = lchecker exfalso
let instantiate_l t what    = lchecker (inst t what)
let intro_l any every where = lchecker (intro any every where)
let intros_l                = lchecker intros
let left_l where            = lchecker (cdir false where)
(* let pose_l name t           = lchecker (pose name t) *)
let rename_l pr1            = lchecker (crename pr1)
let revert_l ls             = lchecker (revert ls)
let rewrite_l rev g where wt= lchecker (rewrite g rev wt where)
let right_l where           = lchecker (cdir true where)
let split_l any every where = lchecker (split_logic any every where)
let split_all_full_l        = lchecker split_all_full
let split_all_right_l       = lchecker split_all_right
let split_goal_full_l       = lchecker split_goal_full
let split_goal_right_l      = lchecker split_goal_right
let split_premise_full_l    = lchecker split_premise_full
let split_premise_right_l   = lchecker split_premise_right
let swap_l where            = lchecker (swap where)
let trivial_l               = lchecker trivial

(** Register certified transformations *)

let register_caml () =
  let open Args_wrapper in
  let open Trans in
  wrap_and_register
    ~desc:"induction <term1> [from] <term2>@ \
           performs@ a@ strong@ induction@ on@ the@ integer@ <term1>@ \
           starting@ from@ the@ integer@ <term2>.@ <term2>@ is@ optional@ \
           and@ defaults@ to@ 0."
    "induction_ccert"
    (Tterm (Topt ("from", Tterm Tenvtrans_l))) induction_c;

  wrap_and_register ~desc:"print given term to debug" "print_ccert"
    (Toptbool ("any", (Toptbool ("all", (Topt ("in", Tprsymbol (Ttrans_l)))))))
    print_c;

  wrap_and_register ~desc:"A OCaml certified version of transformation assert"
    "assert_ccert" (Tformula Ttrans_l) assert_c;

  register_transform_l "assumption_ccert" assumption_c
    ~desc:"A OCaml certified version of coq tactic [assumption]";

  register_transform_l "blast_ccert" blast_c
    ~desc:"A OCaml certified transformation that decomposes structurally \
           logical formulas";

  wrap_and_register "case_ccert" (Tformula Ttrans_l) case_c
    ~desc:"A OCaml certified version of transformation case";

  wrap_and_register  "clear_ccert" (Tprlist Ttrans_l) clear_c
    ~desc:"A OCaml certified version of (simplified) coq tactic [clear]";


  register_transform_l "contradict_ccert" contradict_c
    ~desc:"A OCaml certified transformation that closes some contradictory \
           goals";

  wrap_and_register "destruct_all_ccert"
    (Toptbool ("any", (Toptbool ("all", (Topt ("in", Tprsymbol (Ttrans_l)))))))
    destruct_all_c
    ~desc:"A OCaml certified transformation to destruct a logical constructor";

  register_transform_l "exfalso_ccert" exfalso_c
    ~desc:"A OCaml certified version of coq tactic [exfalso]";

  wrap_and_register "instantiate_ccert"
    (Tterm (Topt ("in", Tprsymbol Ttrans_l))) instantiate_c
    ~desc:"A OCaml certified version of transformation instantiate";

  wrap_and_register "intro_ccert"
    (Toptbool ("any", (Toptbool ("all", (Topt ("in", Tprsymbol (Ttrans_l)))))))
    intro_c
    ~desc:"A OCaml certified version of (simplified) coq tactic [intro]";

  register_transform_l "intros_ccert" intros_c
    ~desc:"A OCaml certified version of coq tactic [intros]";

  wrap_and_register "left_ccert" (Topt ("in", Tprsymbol (Ttrans_l))) left_c
    ~desc:"A OCaml certified version of coq tactic [left]";

  (* wrap_and_register "pose_ccert" (Tstring (Tformula Ttrans_l)) pose_c
   *   ~desc:"A OCaml certified version of (simplified) coq tactic [pose]"; *)

  wrap_and_register "rename_ccert" (Tprsymbol (Ttrans_l)) rename_c
    ~desc:"A OCaml certified transformation to rename an hypothesis";

  wrap_and_register "revert_ccert" (Tlsymbol (Ttrans_l)) revert_c
    ~desc:"A OCaml certified transformation to generalize a variable";

  wrap_and_register "rewrite_ccert"
    (Toptbool ("<-", (Tprsymbol (Topt ("in", Tprsymbol
    (Topt ("with", Ttermlist (Ttrans_l)))))))) rewrite_c
    ~desc:"A OCaml certified version of transformation rewrite";

  wrap_and_register"right_ccert" (Topt ("in", Tprsymbol (Ttrans_l))) right_c
    ~desc:"A OCaml certified version of coq tactic [right]";

  wrap_and_register "split_ccert" (Toptbool ("any", (Toptbool ("all",
    Topt ("in", Tprsymbol Ttrans_l))))) split_c
    ~desc:"A OCaml certified version of (simplified) coq tactic [split]";

  register_transform_l "split_all_full_ccert" split_all_full_c
    ~desc:"The OCaml certified version of split_all_full";

  register_transform_l "split_all_right_ccert" split_all_right_c
    ~desc:"The OCaml certified version of split_all_right";

  register_transform_l "split_goal_full_ccert" split_goal_full_c
    ~desc:"The OCaml certified version of split_goal_full";

  register_transform_l "split_goal_right_ccert" split_goal_right_c
    ~desc:"The OCaml certified version of split_goal_right";

  register_transform_l "split_premise_full_ccert" split_premise_full_c
    ~desc:"The OCaml certified version of split_premise_full";

  register_transform_l "split_premise_right_ccert" split_premise_right_c
    ~desc:"The OCaml certified version of split_premise_right";

  wrap_and_register "swap_ccert" (Topt ("in", Tprsymbol (Ttrans_l))) swap_c
    ~desc:"A OCaml certified transformation that negates and swaps an \
           hypothesis from the context to the goal";

  register_transform_l "trivial_ccert" trivial_c
    ~desc:"A OCaml certified version of (simplified) coq tactic [trivial]"


let register_lambdapi () =
  let open Args_wrapper in
  let open Trans in

  wrap_and_register
    ~desc:"induction <term1> [from] <term2>@ \
           performs@ a@ strong@ induction@ on@ the@ integer@ <term1>@ \
           starting@ from@ the@ integer@ <term2>.@ <term2>@ is@ optional@ \
           and@ defaults@ to@ 0."
    "induction_lcert"
    (Tterm (Topt ("from", Tterm Tenvtrans_l))) induction_l;

  wrap_and_register "assert_lcert" (Tformula Ttrans_l) assert_l
    ~desc:"A Lambdapi certified version of transformation assert";

  register_transform_l "assumption_lcert" assumption_l
    ~desc:"A Lambdapi certified version of coq tactic [assumption]";

  register_transform_l "blast_lcert" blast_l
    ~desc:"A Lambdapi certified transformation that decomposes structurally \
           logical formulas";

  wrap_and_register "case_lcert" (Tformula Ttrans_l) case_l
    ~desc:"A Lambdapi certified version of transformation case";

  wrap_and_register "clear_lcert" (Tprlist Ttrans_l) clear_l
    ~desc:"A Lambdapi certified version of (simplified) coq tactic [clear]";

  register_transform_l "contradict_lcert" contradict_l
    ~desc:"A Lambdapi certified transformation that closes some contradictory \
           goals";

  wrap_and_register "destruct_all_lcert"
    (Toptbool ("any", (Toptbool ("all", (Topt ("in", Tprsymbol (Ttrans_l)))))))
    destruct_all_l ~desc:"A Lambdapi certified transformation to destruct a \
                          logical constructor";

  register_transform_l "exfalso_lcert" exfalso_l
    ~desc:"A Lambdapi certified version of coq tactic [exfalso]";

  wrap_and_register "instantiate_lcert"
    (Tterm (Topt ("in", Tprsymbol Ttrans_l))) instantiate_l
    ~desc:"A Lambdapi certified version of transformation instantiate";

  wrap_and_register "intro_lcert" (Toptbool ("any", (Toptbool ("all",
    Topt ("in", Tprsymbol Ttrans_l))))) intro_l
    ~desc:"A Lambdapi certified version of (simplified) coq tactic [intro]";

  register_transform_l "intros_lcert" intros_l
    ~desc:"A Lambdapi certified version of coq tactic [intros]";

  wrap_and_register "left_lcert" (Topt ("in", Tprsymbol (Ttrans_l)))
    left_l  ~desc:"A Lambdapi certified version of coq tactic [left]";

  (* wrap_and_register "pose_lcert" (Tstring (Tformula Ttrans_l)) pose_l
   *  ~desc:"A Lambdapi certified version of (simplified) coq tactic [pose]"; *)

  wrap_and_register "rename_lcert" (Tprsymbol (Ttrans_l)) rename_l
    ~desc:"A Lambdapi certified transformation to rename an hypothesis";

  wrap_and_register "revert_lcert" (Tlsymbol (Ttrans_l)) revert_l
    ~desc:"A Lambdapi certified transformation to generalize a variable";

  wrap_and_register "rewrite_lcert" (Toptbool ("<-", (Tprsymbol (
    Topt ("in", Tprsymbol (Topt ("with", Ttermlist (Ttrans_l)))))))) rewrite_l
    ~desc:"A Lambdapi certified version of transformation rewrite";

  wrap_and_register "right_lcert" (Topt ("in", Tprsymbol (Ttrans_l)))
    right_l ~desc:"A Lambdapi certified version of coq tactic [right]";

  wrap_and_register "split_lcert"
    (Toptbool ("any", (Toptbool ("all", Topt ("in", Tprsymbol Ttrans_l)))))
    split_l
    ~desc:"A Lambdapi certified version of (simplified) coq tactic [split]";

  register_transform_l "split_all_full_lcert" split_all_full_l
    ~desc:"The Lambdapi certified version of split_all_full";

  register_transform_l "split_all_right_lcert" split_all_right_l
    ~desc:"The Lambdapi certified version of split_all_right";

  register_transform_l "split_goal_full_lcert" split_goal_full_l
    ~desc:"The Lambdapi certified version of split_goal_full";

  register_transform_l "split_goal_right_lcert" split_goal_right_l
    ~desc:"The Lambdapi certified version of split_goal_right";

  register_transform_l "split_premise_full_lcert" split_premise_full_l
    ~desc:"The Lambdapi certified version of split_premise_full";

  register_transform_l "split_premise_right_lcert" split_premise_right_l
    ~desc:"The Lambdapi certified version of split_premise_right";

  wrap_and_register "swap_lcert" (Topt ("in", Tprsymbol (Ttrans_l)))
    swap_l ~desc:"A OCaml certified transformation that negates and swaps an \
                  hypothesis from the context to the goal";

  register_transform_l "trivial_lcert" trivial_l
    ~desc:"A Lambdapi certified version of (simplified) coq tactic [trivial]"

let register_all : unit =
  if !Whyconf.Args.opt_cert_trans then begin
      register_caml ();

      let open Format in
      printf "Checking for lambdapi...@.";
      let lpv = Sysutil.uniquify "/tmp/lambdapi_version.txt" in
      let comm = sprintf "lambdapi --version > %s 2> /dev/null" lpv in
      if Sys.command comm = 0
      then let vers = Sysutil.file_contents lpv in
           let _ = Sys.remove lpv in
           let _ = printf "Found version: %s@." vers in
           let lp_folder = Filename.(concat Config.datadir "lambdapi") in
           let comm = sprintf "make install -C %s > /dev/null 2>&1" lp_folder in
           let _ = Sys.command comm in
           register_lambdapi ()
      else printf "Can't find lambdapi... continuing without lambdapi checker@."
    end
