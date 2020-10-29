open Why3

open Cert_abstract
open Cert_certificates
open Cert_split
open Cert_transformations
open Cert_verif_caml
open Cert_verif_lambdapi


(** Certified transformations *)

let no_dbg = None, None
let cert_dbg = Some eprcertif, None
let cta_dbg = None, Some eplcta
let all_dbg = Some eprcertif, Some eplcta

let cchecker trans = Trans.store (checker_ctrans no_dbg make_core checker_caml trans)
let lchecker trans = Trans.store (checker_ctrans no_dbg make_core checker_lambdapi trans)

let print_c any every where = cchecker (tprint any every where)
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
let left_c where            = cchecker (dir false where)
(* let pose_c name t           = cchecker (pose name t) *)
let rename_c pr1            = cchecker (rename pr1)
let revert_c ls             = cchecker (revert ls)
let rewrite_c rev g where   = cchecker (rewrite g rev where)
let right_c where           = cchecker (dir true where)
let split_c any every where = cchecker (split_logic any every where)
let split_all_full_c        = cchecker split_all_full
let split_all_right_c       = cchecker split_all_right
let split_goal_full_c       = cchecker split_goal_full
let split_goal_right_c      = cchecker split_goal_right
let split_premise_full_c    = cchecker split_premise_full
let split_premise_right_c   = cchecker split_premise_right
let swap_c where            = cchecker (swap where)
let trivial_c               = cchecker trivial


let assert_l t              = lchecker (cut t)
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
let left_l where            = lchecker (dir false where)
(* let pose_l name t           = lchecker (pose name t) *)
let rename_l pr1            = lchecker (rename pr1)
let revert_l ls             = lchecker (revert ls)
let right_l where           = lchecker (dir true where)
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

let register_caml : unit =
  let open Args_wrapper in
  let open Trans in

  wrap_and_register ~desc:"print given term to debug"
    "print_ccert" (Toptbool ("any", (Toptbool ("all", (Topt ("in", Tprsymbol (Ttrans_l)))))))
    print_c;


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


let register_lambdapi : unit =
  let open Args_wrapper in
  let open Trans in

  wrap_and_register ~desc:"A Lambdapi certified version of transformation assert"
    "assert_lcert" (Tformula Ttrans_l)
    assert_l;

  register_transform_l "assumption_lcert" assumption_l
    ~desc:"A Lambdapi certified version of coq tactic [assumption]";

  register_transform_l "blast_lcert" blast_l
    ~desc:"A Lambdapi certified transformation that decomposes structurally logical formulas";

  wrap_and_register ~desc:"A Lambdapi certified version of transformation case"
    "case_lcert" (Tformula Ttrans_l)
    case_l;

  wrap_and_register ~desc:"A Lambdapi certified version of (simplified) coq tactic [clear]"
    "clear_lcert" (Tprlist Ttrans_l)
    clear_l;

  register_transform_l "contradict_lcert" contradict_l
    ~desc:"A Lambdapi certified transformation that closes some contradictory goals";

  wrap_and_register ~desc:"A Lambdapi certified transformation to destruct a logical constructor"
    "destruct_all_lcert" (Toptbool ("any", (Toptbool ("all", (Topt ("in", Tprsymbol (Ttrans_l)))))))
    destruct_all_l;

  register_transform_l "exfalso_lcert" exfalso_l
    ~desc:"A Lambdapi certified version of coq tactic [exfalso]";

  wrap_and_register ~desc:"A Lambdapi certified version of transformation instantiate"
    "instantiate_lcert" (Tterm (Topt ("in", Tprsymbol Ttrans_l)))
    instantiate_l;

  wrap_and_register ~desc:"A Lambdapi certified version of (simplified) coq tactic [intro]"
    "intro_lcert" (Toptbool ("any", (Toptbool ("all", ((Topt ("in", Tprsymbol (Ttrans_l))))))))
    intro_l;

  register_transform_l "intros_lcert" intros_l
    ~desc:"A Lambdapi certified version of coq tactic [intros]";

  wrap_and_register ~desc:"A Lambdapi certified version of coq tactic [left]"
    "left_lcert" (Topt ("in", Tprsymbol (Ttrans_l)))
    left_l;

  (* wrap_and_register ~desc:"A Lambdapi certified version of (simplified) coq tactic [pose]"
   *   "pose_lcert" (Tstring (Tformula Ttrans_l))
   *   pose_l; *)

  wrap_and_register ~desc:"A Lambdapi certified transformation to rename an hypothesis"
    "rename_lcert" (Tprsymbol (Ttrans_l)) rename_l;

  wrap_and_register ~desc:"A Lambdapi certified transformation to generalize a variable"
    "revert_lcert" (Tlsymbol (Ttrans_l))
    revert_l;

  wrap_and_register ~desc:"A Lambdapi certified version of coq tactic [right]"
    "right_lcert" (Topt ("in", Tprsymbol (Ttrans_l)))
    right_l;

  wrap_and_register ~desc:"A Lambdapi certified version of (simplified) coq tactic [split]"
    "split_lcert" (Toptbool ("any", (Toptbool ("all", ((Topt ("in", Tprsymbol (Ttrans_l))))))))
    split_l;

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

  wrap_and_register ~desc:"A OCaml certified transformation that negates \
                           and swaps an hypothesis from the context to the goal"
    "swap_lcert" (Topt ("in", Tprsymbol (Ttrans_l)))
    swap_l;

  register_transform_l "trivial_lcert" trivial_l
    ~desc:"A Lambdapi certified version of (simplified) coq tactic [trivial]"
