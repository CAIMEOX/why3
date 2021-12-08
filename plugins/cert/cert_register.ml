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
open Cert_compute
open Cert_verif_caml
open Cert_verif_lambdapi

let checker_nothing (_ : kcert) (_ : cterm ctask) (_ : cterm ctask list) = ()

(** Certified transformations *)

let no_dbg = None, None
(* let cert_dbg = Some eprcertif, None
 * let cta_dbg = None, Some eplcta
 * let all_dbg = Some eprcertif, Some eplcta *)

(** Get a certified transformation from a transformation with a certificate *)

let checker_ctrans
      ?env
      (debug :   (scert -> unit) option *
                 (cterm ctask -> cterm ctask list -> unit) option )
      (* is_lp *)
      (checker : kcert -> cterm ctask -> cterm ctask list -> unit)
      (ctr : ctrans)
      (init_t : task) =
  try
    let dbg_cert, dbg_cta = debug in
    (* let t1 = Unix.times () in *)
    let res_t, certif = Trans.apply ctr init_t in
    (* let t2 = Unix.times () in *)
    Opt.iter (fun eprcertif -> eprcertif certif) dbg_cert;
    let abstract_task = abstract_task env in
    let init_ct = abstract_task init_t in
    let res_ct = List.map (fun t -> abstract_terms_task (abstract_task t)) res_t in
    let kernel_certif = make_kernel_cert init_ct res_ct certif in
    let init_ct = abstract_terms_task init_ct in
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
  with e -> forget_all ip;
            forget_all hip;
            raise e

exception Unrecognized_checker of string

let make_certifying ?env checker trans = match checker with
  | None -> Trans.store (checker_ctrans ?env no_dbg checker_nothing trans)
  | Some "lp" -> Trans.store (checker_ctrans ?env no_dbg checker_lambdapi trans)
  | Some "ml" -> Trans.store (checker_ctrans ?env no_dbg checker_caml trans)
  | Some s -> raise (Unrecognized_checker s)

let cassert chk t              = make_certifying chk (cassert t)
let cassumption chk            = make_certifying chk assumption
let cblast chk                 = make_certifying chk blast
let ccase chk t                = make_certifying chk (case t)
let cclear chk l               = make_certifying chk (clear l)
let ccompute chk specified steps where env =
  make_certifying ~env:env chk (ccompute specified steps where env)
let ccontradict chk            = make_certifying chk contradict
let cdestruct_all chk any every where =
  make_certifying chk (destruct_all any every where)
let cexfalso chk               = make_certifying chk exfalso
let cinduction chk x bound env = make_certifying chk ~env:env (induction x bound env)
let cinstantiate chk t what    = make_certifying chk (inst t what)
let cintro chk any every where = make_certifying chk (intro any every where)
let cintros chk                = make_certifying chk intros
let cleft chk where            = make_certifying chk (cdir false where)
let cprint chk any every where = make_certifying chk (tprint any every where)
let crename chk pr1            = make_certifying chk (crename pr1)
let crevert chk ls             = make_certifying chk (revert ls)
let crewrite chk rev g where wt= make_certifying chk (rewrite g rev wt where)
let cright chk where           = make_certifying chk (cdir true where)
let csplit chk any every where = make_certifying chk (split_logic any every where)
let csplit_all_full chk        = make_certifying chk split_all_full
let csplit_all_right chk       = make_certifying chk split_all_right
let csplit_goal_full chk       = make_certifying chk split_goal_full
let csplit_goal_right chk      = make_certifying chk split_goal_right
let csplit_premise_full chk    = make_certifying chk split_premise_full
let csplit_premise_right chk   = make_certifying chk split_premise_right
let cswap chk where            = make_certifying chk (swap where)
let ctrivial chk               = make_certifying chk trivial

(** Register certified transformations *)

let register () =
  let open Args_wrapper in

  wrap_and_register
    "cassert" (Topt ("verif", (Tstring (Tformula Ttrans_l)))) cassert
    ~desc:"A@ certifying@ version@ of@ transformation@ assert";

  wrap_and_register "cassumption" (Topt ("verif", (Tstring Ttrans_l))) cassumption
    ~desc:"A@ certifying@ transformation@ inspired@ by@ Coq@ tactic@ [assumption]";

  wrap_and_register "cblast" (Topt ("verif", (Tstring Ttrans_l))) cblast
    ~desc:"A@ certifying@ transformation@ that@ decomposes@ logical@ formulas@ \
           structurally";

  wrap_and_register "ccase" (Topt ("verif", (Tstring (Tformula Ttrans_l)))) ccase
    ~desc:"A@ certifying@ version@ of@ transformation@ case";

  wrap_and_register "cclear" (Topt ("verif", (Tstring (Tprlist Ttrans_l)))) cclear
    ~desc:"A@ certifying@ transformation@ inspired@ by@ Coq@ tactic@ [clear]";

  wrap_and_register
    "ccompute"
    (Topt ("verif", (Tstring (Toptbool ("specified", Topt ("upto", Tint (Topt ("in", Tprsymbol Tenvtrans_l))))))))
    ccompute
    ~desc:"ccompute [upto int] [specified] [in <name>]@ performs@ computations@ \
           in@ the@ given@ premise (default to the goal), using only@ using@ \
           the@ user-specified@ rules@ if@ the@ flag <specified> is@ present";

  wrap_and_register "ccontradict" (Topt ("verif", (Tstring Ttrans_l))) ccontradict
    ~desc:"A@ certifying@ transformation@ that@ closes@ some@ contradictory@ goals";

  wrap_and_register "cdestruct_all"
    (Topt ("verif", Tstring (Toptbool ("any", (Toptbool ("all", (Topt ("in", Tprsymbol (Ttrans_l)))))))))
    cdestruct_all
    ~desc:"A@ certifying@ transformation@ to@ destruct@ a@ logical@ constructor";

  wrap_and_register "cexfalso" (Topt ("verif", (Tstring Ttrans_l))) cexfalso
    ~desc:"A@ certifying@ transformation@ inspired@ by@ Coq@ tactic@ [exfalso]";

  wrap_and_register
    "cinduction"
    (Topt ("verif", (Tstring (Tterm (Topt ("from", Tterm Tenvtrans_l))))))
    cinduction
    ~desc:"cinduction@ <term1>@ [from]@ <term2>@ performs@ a@ strong@ induction@ \
           on@ the@ integer@ <term1>@ starting@ from@ the@ integer@ <term2>.@ \
           <term2>@ is@ optional@ and@ defaults@ to@ 0.";

  wrap_and_register "cinstantiate"
    (Topt ("verif", Tstring (Tterm (Topt ("in", Tprsymbol Ttrans_l)))))
    cinstantiate
    ~desc:"A@ certifying@ version@ of@ transformation@ instantiate";

  wrap_and_register "cintro"
    (Topt ("verif", Tstring (Toptbool ("any", (Toptbool ("all", (Topt ("in", Tprsymbol (Ttrans_l)))))))))
    cintro
    ~desc:"A@ certifying@ transformation@ inspired by@ Coq@ tactic@ [intro]";

  wrap_and_register "cintros" (Topt ("verif", Tstring Ttrans_l)) cintros
    ~desc:"A@ certifying@ transformation@ inspired@ by@ Coq@ tactic@ [intros]";

  wrap_and_register "cleft"
    (Topt ("verif", Tstring (Topt ("in", Tprsymbol (Ttrans_l))))) cleft
    ~desc:"A@ certifying@ transformation@ inspired@ by@ Coq@ tactic@ [left]";

  wrap_and_register "cprint"
    (Topt ("verif", (Tstring (Toptbool ("any", (Toptbool ("all", (Topt ("in", Tprsymbol (Ttrans_l))))))))))
    cprint
    ~desc:"Prints@ a@ given@ term,@ useful@ for@ debugging";

  wrap_and_register "crename" (Topt ("verif", Tstring (Tprsymbol (Ttrans_l))))
    crename
    ~desc:"A@ certifying@ transformation@ to@ rename@ an@ hypothesis";

  wrap_and_register "crevert" (Topt ("verif", Tstring (Tlsymbol (Ttrans_l))))
    crevert
    ~desc:"A@ certifying@ transformation@ to@ generalize@ a@ variable";

  wrap_and_register "crewrite"
    (Topt ("verif", Tstring (Toptbool ("<-", (Tprsymbol (Topt ("in", Tprsymbol (Topt ("with", Ttermlist (Ttrans_l)))))))))) crewrite
    ~desc:"A@ certifying@ version@ of@ transformation@ rewrite";

  wrap_and_register"cright" (Topt ("verif", Tstring (Topt ("in", Tprsymbol (Ttrans_l))))) cright
    ~desc:"A@ certifying@ transformation@ inspired@ by@ Coq@ tactic@ [right]";

  wrap_and_register "csplit"
    (Topt ("verif", Tstring (Toptbool ("any", (Toptbool ("all", Topt ("in", Tprsymbol Ttrans_l)))))))
    csplit
    ~desc:"A@ certifying@ transformation@ inspired@ by@ Coq@ tactic@ [split]";

  wrap_and_register "csplit_all_full" (Topt ("verif", Tstring Ttrans_l))
    csplit_all_full
    ~desc:"A@ certifying@ version@ of@ transformation@ split_all_full";

  wrap_and_register "csplit_all_right" (Topt ("verif", Tstring Ttrans_l))
    csplit_all_right
    ~desc:"A@ certifying@ version@ of@ transformation@ split_all_right";

  wrap_and_register "csplit_goal_full" (Topt ("verif", Tstring Ttrans_l))
    csplit_goal_full
    ~desc:"A@ certifying@ version@ of@ transformation@ split_goal_full";

  wrap_and_register "csplit_goal_right" (Topt ("verif", Tstring Ttrans_l))
    csplit_goal_right
    ~desc:"A@ certifying@ version@ of@ transformation@ split_goal_right";

  wrap_and_register "csplit_premise_full" (Topt ("verif", Tstring Ttrans_l))
    csplit_premise_full
    ~desc:"A@ certifying@ version@ of@ transformation@ split_premise_full";

  wrap_and_register "csplit_premise_right" (Topt ("verif", Tstring Ttrans_l))
    csplit_premise_right
    ~desc:"A@ certifying@ version@ of@ transformation@ split_premise_right";

  wrap_and_register "cswap"
    (Topt ("verif", Tstring (Topt ("in", Tprsymbol (Ttrans_l))))) cswap
    ~desc:"A@ certifying@ transformation@ that@ negates@ and@ swaps@ an@ \
           hypothesis@ from@ the@ context@ to@ the@ goal";

  wrap_and_register "ctrivial" (Topt ("verif", Tstring Ttrans_l)) ctrivial
    ~desc:"A@ certifying@ transformation@ inspired by@ Coq@ tactic@ [trivial]"


let _ : unit =
  let open Format in
  begin try
    let lpv = Sysutil.uniquify "/tmp/lambdapi_version.txt" in
    let lp_version = sprintf "lambdapi --version > %s 2> /dev/null" lpv in
    assert (Sys.command lp_version = 0);
    let vers = Sysutil.file_contents lpv in
    let _ = Sys.remove lpv in
    let lp_folder = Filename.(concat Config.datadir "lambdapi") in
    let lp_install = sprintf "make install -C %s > /dev/null 2>&1" lp_folder in
    assert (Sys.command lp_install = 0);
    printf "Found lambdapi version %s@." vers
  with _ -> ()
  end;

  register ()
