open Why3

open Cert_abstract
open Cert_certificates
open Cert_split
open Cert_transformations
open Cert_verif_caml
open Cert_verif_dedukti


(** Certified transformations *)

(* let cchecker trans = Trans.store (checker_ctrans None make_core checker_caml trans)
 * let dchecker trans = Trans.store (checker_ctrans None make_core checker_dedukti trans) *)

let cchecker trans = Trans.store (checker_ctrans (Some eprcertif) make_core checker_caml trans)
let dchecker trans = Trans.store (checker_ctrans (Some eprcertif) make_core checker_dedukti trans)


let assert_c t              = cchecker (cut t)
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
let left_c where            = cchecker (dir Left where)
(* let pose_c name t           = cchecker (pose name t) *)
let rename_c pr1            = cchecker (rename pr1)
let revert_c ls             = cchecker (revert ls)
let rewrite_c rev g where   = cchecker (rewrite g rev where)
let right_c where           = cchecker (dir Right where)
let split_c any every where = cchecker (split_logic any every where)
let split_all_full_c        = cchecker split_all_full
let split_all_right_c       = cchecker split_all_right
let split_goal_full_c       = cchecker split_goal_full
let split_goal_right_c      = cchecker split_goal_right
let split_premise_full_c    = cchecker split_premise_full
let split_premise_right_c   = cchecker split_premise_right
let swap_c where            = cchecker (swap where)
let trivial_c               = cchecker trivial


let assert_d t              = dchecker (cut t)
let assumption_d            = dchecker assumption
let blast_d                 = dchecker blast
let case_d t                = dchecker (case t)
let clear_d l               = dchecker (clear l)
let contradict_d            = dchecker contradict
let destruct_all_d any every where = dchecker (destruct_all any every where)
let exfalso_d               = dchecker exfalso
let instantiate_d t what    = dchecker (inst t what)
let intro_d any every where = dchecker (intro any every where)
let intros_d                = dchecker intros
let left_d where            = dchecker (dir Left where)
(* let pose_d name t           = dchecker (pose name t) *)
let rename_d pr1            = dchecker (rename pr1)
let revert_d ls             = dchecker (revert ls)
let right_d where           = dchecker (dir Right where)
let split_d any every where = dchecker (split_logic any every where)
let split_all_full_d        = dchecker split_all_full
let split_all_right_d       = dchecker split_all_right
let split_goal_full_d       = dchecker split_goal_full
let split_goal_right_d      = dchecker split_goal_right
let split_premise_full_d    = dchecker split_premise_full
let split_premise_right_d   = dchecker split_premise_right
let swap_d where            = dchecker (swap where)
let trivial_d               = dchecker trivial

(** Register certified transformations *)

let register_caml : unit =
  let open Args_wrapper in
  let open Trans in

  wrap_and_register ~desc:"A OCaml certified version of transformation assert"
    "assert_ccert" (Tformula Ttrans_l) assert_c;

  register_transform_l "assumption_ccert" assumption_c
    ~desc:"A OCaml certified version of coq tactic [assumption]";

  register_transform_l "blast_ccert" blast_c
    ~desc:"A OCaml certified transformation that decomposes structurally logical formulas";

  wrap_and_register ~desc:"A OCaml certified version of transformation case"
    "case_ccert" (Tformula Ttrans_l) case_c;

  wrap_and_register ~desc:"A OCaml certified version of (simplified) coq tactic [clear]"
    "clear_ccert" (Tprlist Ttrans_l) clear_c;

  register_transform_l "contradict_ccert" contradict_c
    ~desc:"A OCaml certified transformation that closes some contradictory goals";

  wrap_and_register ~desc:"A OCaml certified transformation to destruct a logical constructor"
    "destruct_all_ccert" (Toptbool ("any", (Toptbool ("all", (Topt ("in", Tprsymbol (Ttrans_l)))))))
    destruct_all_c;

  register_transform_l "exfalso_ccert" exfalso_c
    ~desc:"A OCaml certified version of coq tactic [exfalso]";

  wrap_and_register ~desc:"A OCaml certified version of transformation instantiate"
    "instantiate_ccert" (Tterm (Topt ("in", Tprsymbol Ttrans_l)))
    instantiate_c;

  wrap_and_register ~desc:"A OCaml certified version of (simplified) coq tactic [intro]"
    "intro_ccert" (Toptbool ("any", (Toptbool ("all", (Topt ("in", Tprsymbol (Ttrans_l)))))))
    intro_c;

  register_transform_l "intros_ccert" intros_c
    ~desc:"A OCaml certified version of coq tactic [intros]";

  wrap_and_register ~desc:"A OCaml certified version of coq tactic [left]"
    "left_ccert" (Topt ("in", Tprsymbol (Ttrans_l))) left_c;

  (* wrap_and_register ~desc:"A OCaml certified version of (simplified) coq tactic [pose]"
   *   "pose_ccert" (Tstring (Tformula Ttrans_l)) pose_c; *)

  wrap_and_register ~desc:"A OCaml certified transformation to rename an hypothesis"
    "rename_ccert" (Tprsymbol (Ttrans_l)) rename_c;

  wrap_and_register ~desc:"A OCaml certified transformation to generalize a variable"
    "revert_ccert" (Tlsymbol (Ttrans_l)) revert_c;

  wrap_and_register ~desc:"A OCaml certified version of transformation rewrite"
    "rewrite_ccert" (Toptbool ("<-", (Tprsymbol (Topt ("in", Tprsymbol (Ttrans_l)))))) rewrite_c;

  wrap_and_register ~desc:"A OCaml certified version of coq tactic [right]"
    "right_ccert" (Topt ("in", Tprsymbol (Ttrans_l))) right_c;

  wrap_and_register ~desc:"A OCaml certified version of (simplified) coq tactic [split]"
    "split_ccert" (Toptbool ("any", (Toptbool ("all", ((Topt ("in", Tprsymbol (Ttrans_l))))))))
    split_c;

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

  wrap_and_register ~desc:"A OCaml certified transformation that negates \
                           and swaps an hypothesis from the context to the goal"
    "swap_ccert" (Topt ("in", Tprsymbol (Ttrans_l))) swap_c;

  register_transform_l "trivial_ccert" trivial_c
    ~desc:"A OCaml certified version of (simplified) coq tactic [trivial]"


let register_dedukti : unit =
  let open Args_wrapper in
  let open Trans in

  wrap_and_register ~desc:"A Dedukti certified version of transformation assert"
    "assert_dcert" (Tformula Ttrans_l)
    assert_d;

  register_transform_l "assumption_dcert" assumption_d
    ~desc:"A Dedukti certified version of coq tactic [assumption]";

  register_transform_l "blast_dcert" blast_d
    ~desc:"A Dedukti certified transformation that decomposes structurally logical formulas";

  wrap_and_register ~desc:"A Dedukti certified version of transformation case"
    "case_dcert" (Tformula Ttrans_l)
    case_d;

  wrap_and_register ~desc:"A Dedukti certified version of (simplified) coq tactic [clear]"
    "clear_dcert" (Tprlist Ttrans_l)
    clear_d;

  register_transform_l "contradict_dcert" contradict_d
    ~desc:"A Dedukti certified transformation that closes some contradictory goals";

  wrap_and_register ~desc:"A Dedukti certified transformation to destruct a logical constructor"
    "destruct_all_dcert" (Toptbool ("any", (Toptbool ("all", (Topt ("in", Tprsymbol (Ttrans_l)))))))
    destruct_all_d;

  register_transform_l "exfalso_dcert" exfalso_d
    ~desc:"A Dedukti certified version of coq tactic [exfalso]";

  wrap_and_register ~desc:"A Dedukti certified version of transformation instantiate"
    "instantiate_dcert" (Tterm (Topt ("in", Tprsymbol Ttrans_l)))
    instantiate_d;

  wrap_and_register ~desc:"A Dedukti certified version of (simplified) coq tactic [intro]"
    "intro_dcert" (Toptbool ("any", (Toptbool ("all", ((Topt ("in", Tprsymbol (Ttrans_l))))))))
    intro_d;

  register_transform_l "intros_dcert" intros_d
    ~desc:"A Dedukti certified version of coq tactic [intros]";

  wrap_and_register ~desc:"A Dedukti certified version of coq tactic [left]"
    "left_dcert" (Topt ("in", Tprsymbol (Ttrans_l)))
    left_d;

  (* wrap_and_register ~desc:"A Dedukti certified version of (simplified) coq tactic [pose]"
   *   "pose_dcert" (Tstring (Tformula Ttrans_l))
   *   pose_d; *)

  wrap_and_register ~desc:"A Dedukti certified transformation to rename an hypothesis"
    "rename_dcert" (Tprsymbol (Ttrans_l)) rename_d;

  wrap_and_register ~desc:"A Dedukti certified transformation to generalize a variable"
    "revert_dcert" (Tlsymbol (Ttrans_l))
    revert_d;

  wrap_and_register ~desc:"A Dedukti certified version of coq tactic [right]"
    "right_dcert" (Topt ("in", Tprsymbol (Ttrans_l)))
    right_d;

  wrap_and_register ~desc:"A Dedukti certified version of (simplified) coq tactic [split]"
    "split_dcert" (Toptbool ("any", (Toptbool ("all", ((Topt ("in", Tprsymbol (Ttrans_l))))))))
    split_d;

  register_transform_l "split_all_full_dcert" split_all_full_d
    ~desc:"The Dedukti certified version of split_all_full";

  register_transform_l "split_all_right_dcert" split_all_right_d
    ~desc:"The Dedukti certified version of split_all_right";

  register_transform_l "split_goal_full_dcert" split_goal_full_d
    ~desc:"The Dedukti certified version of split_goal_full";

  register_transform_l "split_goal_right_dcert" split_goal_right_d
    ~desc:"The Dedukti certified version of split_goal_right";

  register_transform_l "split_premise_full_dcert" split_premise_full_d
    ~desc:"The Dedukti certified version of split_premise_full";

  register_transform_l "split_premise_right_dcert" split_premise_right_d
    ~desc:"The Dedukti certified version of split_premise_right";

  wrap_and_register ~desc:"A OCaml certified transformation that negates \
                           and swaps an hypothesis from the context to the goal"
    "swap_dcert" (Topt ("in", Tprsymbol (Ttrans_l)))
    swap_d;

  register_transform_l "trivial_dcert" trivial_d
    ~desc:"A Dedukti certified version of (simplified) coq tactic [trivial]"
