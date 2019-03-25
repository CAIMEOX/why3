open Why3
open Cert_syntax
open Cert_transformations
open Cert_verif


(** Certified transformations *)

let checker_ctrans = checker_ctrans check_certif ctask_equal

let assumption_trans          = checker_ctrans assumption
let intro_trans               = checker_ctrans intro
let intros_trans              = checker_ctrans intros
let intuition_trans           = checker_ctrans intuition
let left_trans where          = checker_ctrans (dir Left where)
let right_trans where         = checker_ctrans (dir Right where)
let split_trans where         = checker_ctrans (split_logic where)
let rewrite_trans g rev where = checker_ctrans (rewrite g rev where)
let clear_trans l             = checker_ctrans (clear l)


(** Register certified transformations *)

let () =
  let open Args_wrapper in let open Trans in

  register_transform_l "assumption_cert" (store assumption_trans)
    ~desc:"A certified version of coq tactic [assumption]";

  register_transform_l "intro_cert" (store intro_trans)
    ~desc:"A certified version of (simplified) coq tactic [intro]";

  register_transform_l "intros_cert" (store intros_trans)
    ~desc:"A certified version of coq tactic [intros]";

  register_transform_l "intuition_cert" (store intuition_trans)
    ~desc:"A certified version of (simplified) coq tactic [intuition]";

  wrap_and_register ~desc:"A certified version of coq tactic [left]"
     "left_cert" (Topt ("in", Tprsymbol (Ttrans_l)))
     (fun where -> store (left_trans where));

  wrap_and_register ~desc:"A certified version of coq tactic [right]"
     "right_cert" (Topt ("in", Tprsymbol (Ttrans_l)))
     (fun where -> store (right_trans where));

  wrap_and_register ~desc:"A certified version of (simplified) coq tactic [split]"
    "split_cert" (Topt ("in", Tprsymbol (Ttrans_l)))
    (fun where -> store (split_trans where));

  wrap_and_register ~desc:"A certified version of transformation rewrite"
    "rewrite_cert" (Toptbool ("<-", (Tprsymbol (Topt ("in", Tprsymbol (Ttrans_l))))))
    (fun rev g where -> store (rewrite_trans g rev where));

  wrap_and_register ~desc:"A certified version of (simplified) coq tactic [clear]"
    "clear_cert" (Tprlist Ttrans_l)
    (fun l -> store (clear_trans l))
