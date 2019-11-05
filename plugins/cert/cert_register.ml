open Why3
open Cert_syntax
open Cert_transformations
open Cert_verif_caml
open Cert_verif_dedukti


(** Certified transformations *)

let cchecker = checker_ctrans checker_caml
let dchecker = checker_ctrans checker_dedukti

let contradict_c          = cchecker contradict

let assumption_c          = cchecker assumption
let intro_c where         = cchecker (intro false where)
let left_c where          = cchecker (dir Left where)
let right_c where         = cchecker (dir Right where)
let split_c where         = cchecker (split_logic false where)
let case_c t              = cchecker (case t)
let swap_c where          = cchecker (swap where)
let exfalso_c             = cchecker exfalso
let trivial_c             = cchecker trivial
let intros_c              = cchecker intros
let clear_c l             = cchecker (clear l)
let assert_c t            = cchecker (cut t)
let revert_c ls           = cchecker (revert ls)
let pose_c name t         = cchecker (pose name t)
let instantiate_c t what  = cchecker (inst t what)
let intuition_c           = cchecker intuition
let rewrite_c g rev where = cchecker (rewrite g rev where)


let assumption_d          = dchecker assumption
let intro_d where         = dchecker (intro false where)
let left_d where          = dchecker (dir Left where)
let right_d where         = dchecker (dir Right where)
let split_d where         = dchecker (split_logic false where)
let trivial_d             = dchecker trivial
let exfalso_d             = dchecker exfalso
let intros_d              = dchecker intros
let intuition_d           = dchecker intuition
let swap_d where          = dchecker (swap where)
let revert_d ls           = dchecker (revert ls)
let instantiate_d t what  = dchecker (inst t what)
let assert_d t            = dchecker (cut t)
let case_d t              = dchecker (case t)
let clear_d l             = dchecker (clear l)
let pose_d name t         = dchecker (pose name t)

(** Register certified transformations *)

let register_caml : unit =
  let open Args_wrapper in let open Trans in

  register_transform_l "contradict_ccert" (store contradict_c)
    ~desc:"A OCaml certified transformation that closes some contradictory goals";

  register_transform_l "assumption_ccert" (store assumption_c)
    ~desc:"A OCaml certified version of coq tactic [assumption]";

  register_transform_l "trivial_ccert" (store trivial_c)
    ~desc:"A OCaml certified version of (simplified) coq tactic [trivial]";

  register_transform_l "exfalso_ccert" (store exfalso_c)
    ~desc:"A OCaml certified version of coq tactic [exfalso]";

  register_transform_l "intros_ccert" (store intros_c)
    ~desc:"A OCaml certified version of coq tactic [intros]";

  register_transform_l "intuition_ccert" (store intuition_c)
    ~desc:"A OCaml certified version of (simplified) coq tactic [intuition]";

  wrap_and_register ~desc:"A OCaml certified transformation that negates \
                           and swaps an hypothesis from the context to the goal]"
    "swap_ccert" (Topt ("in", Tprsymbol (Ttrans_l)))
     (fun where -> store (swap_c where));

  wrap_and_register ~desc:"A OCaml certified transformation that generalizes a variable in the goal"
    "revert_ccert" (Tlsymbol (Ttrans_l))
     (fun ls -> store (revert_c ls));

  wrap_and_register ~desc:"A OCaml certified version of (simplified) coq tactic [intro]"
    "intro_ccert" (Topt ("in", Tprsymbol (Ttrans_l)))
     (fun where -> store (intro_c where));

  wrap_and_register ~desc:"A OCaml certified version of coq tactic [left]"
     "left_ccert" (Topt ("in", Tprsymbol (Ttrans_l)))
     (fun where -> store (left_c where));

  wrap_and_register ~desc:"A OCaml certified version of coq tactic [right]"
     "right_ccert" (Topt ("in", Tprsymbol (Ttrans_l)))
     (fun where -> store (right_c where));

  wrap_and_register ~desc:"A OCaml certified version of (simplified) coq tactic [split]"
    "split_ccert" (Topt ("in", Tprsymbol (Ttrans_l)))
    (fun where -> store (split_c where));

  wrap_and_register ~desc:"A OCaml certified version of transformation instantiate"
    "instantiate_ccert" (Tterm (Topt ("in", Tprsymbol Ttrans_l)))
    (fun t_inst where -> store (instantiate_c t_inst where));

  wrap_and_register ~desc:"A OCaml certified version of transformation rewrite"
    "rewrite_ccert" (Toptbool ("<-", (Tprsymbol (Topt ("in", Tprsymbol (Ttrans_l))))))
    (fun rev g where -> store (rewrite_c g rev where));

  wrap_and_register ~desc:"A OCaml certified version of transformation assert"
    "assert_ccert" (Tformula Ttrans_l)
    (fun t -> store (assert_c t));

  wrap_and_register ~desc:"A OCaml certified version of transformation case"
    "case_ccert" (Tformula Ttrans_l)
    (fun t -> store (case_c t));

  wrap_and_register ~desc:"A OCaml certified version of (simplified) coq tactic [clear]"
    "clear_ccert" (Tprlist Ttrans_l)
    (fun l -> store (clear_c l));

  wrap_and_register ~desc:"A OCaml certified version of (simplified) coq tactic [pose]"
    "pose_ccert" (Tstring (Tformula Ttrans_l))
    (fun name t -> store (pose_c name t))


let register_dedukti : unit =
  let open Args_wrapper in let open Trans in

  register_transform_l "assumption_dcert" (store assumption_d)
    ~desc:"A Dedukti certified version of coq tactic [assumption]";

  register_transform_l "trivial_dcert" (store trivial_d)
    ~desc:"A Dedukti certified version of (simplified) coq tactic [trivial]";

  register_transform_l "exfalso_dcert" (store exfalso_d)
    ~desc:"A Dedukti certified version of coq tactic [exfalso]";

  register_transform_l "intros_dcert" (store intros_d)
    ~desc:"A Dedukti certified version of coq tactic [intros]";

  register_transform_l "intuition_dcert" (store intuition_d)
    ~desc:"A Dedukti certified version of (simplified) coq tactic [intuition]";

  wrap_and_register ~desc:"A Dedukti certified transformation that negates \
                           and swaps an hypothesis from the context to the goal]"
    "swap_dcert" (Topt ("in", Tprsymbol (Ttrans_l)))
     (fun where -> store (swap_d where));

  wrap_and_register ~desc:"A Dedukti certified transformation that generalizes a variable in the goal"
    "revert_dcert" (Tlsymbol (Ttrans_l))
     (fun ls -> store (revert_d ls));

  wrap_and_register ~desc:"A Dedukti certified version of (simplified) coq tactic [intro]"
    "intro_dcert" (Topt ("in", Tprsymbol (Ttrans_l)))
     (fun where -> store (intro_d where));

  wrap_and_register ~desc:"A Dedukti certified version of coq tactic [left]"
     "left_dcert" (Topt ("in", Tprsymbol (Ttrans_l)))
     (fun where -> store (left_d where));

  wrap_and_register ~desc:"A Dedukti certified version of coq tactic [right]"
     "right_dcert" (Topt ("in", Tprsymbol (Ttrans_l)))
     (fun where -> store (right_d where));

  wrap_and_register ~desc:"A Dedukti certified version of (simplified) coq tactic [split]"
    "split_dcert" (Topt ("in", Tprsymbol (Ttrans_l)))
    (fun where -> store (split_d where));

  wrap_and_register ~desc:"A Dedukti certified version of transformation instantiate"
    "instantiate_dcert" (Tterm (Topt ("in", Tprsymbol Ttrans_l)))
    (fun t_inst where -> store (instantiate_d t_inst where));

  wrap_and_register ~desc:"A Dedukti certified version of transformation assert"
    "assert_dcert" (Tformula Ttrans_l)
    (fun t -> store (assert_d t));

  wrap_and_register ~desc:"A Dedukti certified version of transformation case"
    "case_dcert" (Tformula Ttrans_l)
    (fun t -> store (case_d t));

  wrap_and_register ~desc:"A Dedukti certified version of (simplified) coq tactic [clear]"
    "clear_dcert" (Tprlist Ttrans_l)
    (fun l -> store (clear_d l));

  wrap_and_register ~desc:"A Dedukti certified version of (simplified) coq tactic [pose]"
    "pose_dcert" (Tstring (Tformula Ttrans_l))
    (fun name t -> store (pose_d name t))

