open Why3

open Compute

open Cert_certificates
open Cert_trans_utils


let ccompute specified steps where env =
  Trans.store (fun task ->
      let pr = default_goal task where in
      let tr = if specified then normalize_hyp_few steps (Some pr) env
               else normalize_hyp steps (Some pr) env in
      Trans.apply tr task, compute pr)
