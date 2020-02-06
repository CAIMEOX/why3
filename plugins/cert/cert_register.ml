open Why3
open Cert_syntax
open Cert_transformations
open Cert_verif_caml
open Cert_verif_dedukti


(** Certified transformations *)

let cchecker trans = Trans.store (checker_ctrans checker_caml trans)
let dchecker trans = Trans.store (checker_ctrans checker_dedukti trans)


let split_goal_full_c     = cchecker Cert_split.split_goal_full
let split_goal_full_d     = dchecker Cert_split.split_goal_full

let split_all_full_c     = cchecker Cert_split.split_all_full
let split_all_full_d     = dchecker Cert_split.split_all_full

let assert_c t            = cchecker (cut t)
let assumption_c          = cchecker assumption
let blast_c               = cchecker blast
let case_c t              = cchecker (case t)
let clear_c l             = cchecker (clear l)
let contradict_c          = cchecker contradict
let exfalso_c             = cchecker exfalso
let instantiate_c t what  = cchecker (inst t what)
let intro_c where         = cchecker (intro false where)
let intros_c              = cchecker intros
let left_c where          = cchecker (dir Left where)
let pose_c name t         = cchecker (pose name t)
let revert_c ls           = cchecker (revert ls)
let rewrite_c rev g where = cchecker (rewrite g rev where)
let right_c where         = cchecker (dir Right where)
let split_c where         = cchecker (split_logic false where)
let swap_c where          = cchecker (swap where)
let trivial_c             = cchecker trivial

let assert_d t            = dchecker (cut t)
let assumption_d          = dchecker assumption
let blast_d               = dchecker blast
let case_d t              = dchecker (case t)
let clear_d l             = dchecker (clear l)
let contradict_d          = dchecker contradict
let exfalso_d             = dchecker exfalso
let instantiate_d t what  = dchecker (inst t what)
let intro_d where         = dchecker (intro false where)
let intros_d              = dchecker intros
let left_d where          = dchecker (dir Left where)
let pose_d name t         = dchecker (pose name t)
let revert_d ls           = dchecker (revert ls)
let right_d where         = dchecker (dir Right where)
let split_d where         = dchecker (split_logic false where)
let swap_d where          = dchecker (swap where)
let trivial_d             = dchecker trivial

(** Register certified transformations *)

let register_caml : unit =
  let open Args_wrapper in let open Trans in

  register_transform_l "split_goal_full_ccert" split_goal_full_c
    ~desc:"The OCaml certified version of split_goal";

  register_transform_l "split_goal_full_dcert" split_goal_full_d
    ~desc:"The Dedukti certified version of split_goal";

  register_transform_l "split_all_full_ccert" split_all_full_c
    ~desc:"The OCaml certified version of split_all";

  register_transform_l "split_all_full_dcert" split_all_full_d
    ~desc:"The Dedukti certified version of split_all";




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

  register_transform_l "exfalso_ccert" exfalso_c
    ~desc:"A OCaml certified version of coq tactic [exfalso]";

  wrap_and_register ~desc:"A OCaml certified version of transformation instantiate"
    "instantiate_ccert" (Tterm (Topt ("in", Tprsymbol Ttrans_l)))
    instantiate_c;

  wrap_and_register ~desc:"A OCaml certified version of (simplified) coq tactic [intro]"
    "intro_ccert" (Topt ("in", Tprsymbol (Ttrans_l))) intro_c;

  register_transform_l "intros_ccert" intros_c
    ~desc:"A OCaml certified version of coq tactic [intros]";

  wrap_and_register ~desc:"A OCaml certified version of coq tactic [left]"
     "left_ccert" (Topt ("in", Tprsymbol (Ttrans_l))) left_c;

  wrap_and_register ~desc:"A OCaml certified version of (simplified) coq tactic [pose]"
    "pose_ccert" (Tstring (Tformula Ttrans_l)) pose_c;

  wrap_and_register ~desc:"A OCaml certified transformation to generalize a variable"
    "revert_ccert" (Tlsymbol (Ttrans_l)) revert_c;

  wrap_and_register ~desc:"A OCaml certified version of transformation rewrite"
    "rewrite_ccert" (Toptbool ("<-", (Tprsymbol (Topt ("in", Tprsymbol (Ttrans_l)))))) rewrite_c;

  wrap_and_register ~desc:"A OCaml certified version of coq tactic [right]"
     "right_ccert" (Topt ("in", Tprsymbol (Ttrans_l))) right_c;

  wrap_and_register ~desc:"A OCaml certified version of (simplified) coq tactic [split]"
    "split_ccert" (Topt ("in", Tprsymbol (Ttrans_l))) split_c;

  wrap_and_register ~desc:"A OCaml certified transformation that negates \
                           and swaps an hypothesis from the context to the goal]"
    "swap_ccert" (Topt ("in", Tprsymbol (Ttrans_l))) swap_c;

  register_transform_l "trivial_ccert" trivial_c
    ~desc:"A OCaml certified version of (simplified) coq tactic [trivial]"


let register_dedukti : unit =
  let open Args_wrapper in let open Trans in

  register_transform_l "contradict_dcert" contradict_d
    ~desc:"A Dedukti certified transformation that closes some contradictory goals";

  register_transform_l "assumption_dcert" assumption_d
    ~desc:"A Dedukti certified version of coq tactic [assumption]";

  register_transform_l "trivial_dcert" trivial_d
    ~desc:"A Dedukti certified version of (simplified) coq tactic [trivial]";

  register_transform_l "exfalso_dcert" exfalso_d
    ~desc:"A Dedukti certified version of coq tactic [exfalso]";

  register_transform_l "intros_dcert" intros_d
    ~desc:"A Dedukti certified version of coq tactic [intros]";

  register_transform_l "blast_dcert" blast_d
    ~desc:"A Dedukti certified transformation that decomposes structurally logical formulas";

  wrap_and_register ~desc:"A Dedukti certified transformation that negates \
                           and swaps an hypothesis from the context to the goal]"
    "swap_dcert" (Topt ("in", Tprsymbol (Ttrans_l)))
     swap_d;

  wrap_and_register ~desc:"A Dedukti certified transformation to generalize a variable"
    "revert_dcert" (Tlsymbol (Ttrans_l))
     revert_d;

  wrap_and_register ~desc:"A Dedukti certified version of (simplified) coq tactic [intro]"
    "intro_dcert" (Topt ("in", Tprsymbol (Ttrans_l)))
     intro_d;

  wrap_and_register ~desc:"A Dedukti certified version of coq tactic [left]"
     "left_dcert" (Topt ("in", Tprsymbol (Ttrans_l)))
     left_d;

  wrap_and_register ~desc:"A Dedukti certified version of coq tactic [right]"
     "right_dcert" (Topt ("in", Tprsymbol (Ttrans_l)))
     right_d;

  wrap_and_register ~desc:"A Dedukti certified version of (simplified) coq tactic [split]"
    "split_dcert" (Topt ("in", Tprsymbol (Ttrans_l)))
    split_d;

  wrap_and_register ~desc:"A Dedukti certified version of transformation instantiate"
    "instantiate_dcert" (Tterm (Topt ("in", Tprsymbol Ttrans_l)))
    instantiate_d;

  wrap_and_register ~desc:"A Dedukti certified version of transformation assert"
    "assert_dcert" (Tformula Ttrans_l)
    assert_d;

  wrap_and_register ~desc:"A Dedukti certified version of transformation case"
    "case_dcert" (Tformula Ttrans_l)
    case_d;

  wrap_and_register ~desc:"A Dedukti certified version of (simplified) coq tactic [clear]"
    "clear_dcert" (Tprlist Ttrans_l)
    clear_d;

  wrap_and_register ~desc:"A Dedukti certified version of (simplified) coq tactic [pose]"
    "pose_dcert" (Tstring (Tformula Ttrans_l))
    pose_d

