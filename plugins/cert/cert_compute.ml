open Why3
open Ident
open Decl
open Task
open Compute

open Cert_certificates
open Cert_trans_utils

(* One function for computing on a given decl, using or not user-specified
   rules. See compute.ml for a description of the parameters. *)
let ccompute specified steps where env =
  Trans.store (fun task ->
      let pr = default_goal task where in
      let tr = if specified then normalize_hyp_few steps (Some pr) env
               else normalize_hyp steps (Some pr) env in
      let ntask = Trans.apply tr task in
      let decl = Mid.find pr.pr_name (task_known task) in
      let nt = match decl.d_node with
        | Dprop (_, pr', t) when pr_equal pr' pr -> t
        | _ -> assert false in
      ntask , conv pr nt)
