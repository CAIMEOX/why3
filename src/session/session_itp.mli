



(** {1 New Proof sessions ("Refectoire")} *)


(** {2 upper level structure of sessions}

   A [session] contains a collection of files, a [file] contains a
collection of theories, a [theory] contains a collection of goals. The
structure of goals remain abstract, each goal being identified by
unique identifiers of type [proofNodeId]

*)

type session

type proofNodeID

type theory

val theory_name : theory -> Ident.ident
val theory_goals : theory -> proofNodeID list

type file = private {
  file_name     : string;
  file_format   : string option;
  file_theories : theory list;
}

val get_files : session -> file Stdlib.Hstr.t



(** {2 Proof trees}

Each goal

*)



type proof_attempt
type transID

type trans_arg =
  | TAint      of int
  | TAstring   of string
  | TAterm     of Term.term
  | TAty       of Ty.ty
  | TAtysymbol of Ty.tysymbol
  (* | ... *)
(* note: la fonction register des transformations doit permettre de
   declarer les types des arguments

   type trans_arg_type = TTint | TTstring | TTterm | TTty | TTtysymbol
   | TTlsymbol | TTprsymbol

*)


type tree = {
    tree_node_id : proofNodeID;
    tree_goal_name : string;
    tree_proof_attempts : proof_attempt list; (* proof attempts on this node *)
    tree_transformations : (transID * string * tree list) list;
                                (* transformations on this node *)
  }
(* a tree is a complete proof whenever at least one proof_attempf or
  one transformation proves the goal, where a transformation proves a
  goal when all subgoals have a complete proof.  In other word, the
  list of proof_attempt and transformation are "disjunctive" but the
  list of tree below a transformation is "conjunctive" *)


val get_tree : session -> proofNodeID -> tree
(** [get_tree s id] returns the proof tree of the goal identified by
    [id] *)

val get_task : session -> proofNodeID -> Task.task

(* temp *)
val get_node : session -> int -> proofNodeID
val get_trans : session -> int -> transID
val print_tree : session -> Format.formatter -> tree -> unit
val print_session : Format.formatter -> session -> unit

(* val get_proof_attempts : session -> proofNodeID -> proof_attempt Whyconf.Hprover.t *)
val get_transformations : session -> proofNodeID -> transID list
val get_sub_tasks : session -> transID -> proofNodeID list

val empty_session : ?shape_version:int -> unit -> session

val add_file_section :
  session -> string -> (Theory.theory list) -> Env.fformat option -> unit
(** [add_file_section s fn ths] adds a new 'file' section in session
    [s], named [fn], containing fresh theory subsections corresponding
    to theories [ths]. The tasks of each theory nodes generated are
    computed using [Task.split_theory] *)

val graft_proof_attempt : session -> proofNodeID -> Whyconf.prover ->
  timelimit:int -> unit
(** [graft_proof_attempt s id pr t] adds a proof attempt with prover
    [pr] and timelimit [t] in the session [s] as a child of the task
    [id]. If there already a proof attempt with the same prover,
    it updates it with the new timelimit. *)

val update_proof_attempt : session -> proofNodeID -> Whyconf.prover ->
  Call_provers.prover_result -> unit
(** [update_proof_attempt s id pr st] update the status of the
    corresponding proof attempt with [st]. *)

val graft_transf : session -> proofNodeID -> string -> trans_arg list ->
   transID
(** [graft_transf s id name l] adds the transformation [name] as a
    child of the task [id] of the session [s]. [l] is the list of
    argument of the transformation. The subtasks are initialized to
    the empty list *)

val set_transf_tasks : session -> transID -> Task.task list -> unit
(** [set_transf_tasks s id tl] sets the tasks of the transformation node
    [id] to [tl] *)

val remove_proof_attempt : session -> proofNodeID -> Whyconf.prover -> unit
(** [remove_proof_attempt s id pr] removes the proof attempt from the
    prover [pr] from the proof node [id] of the session [s] *)

val remove_transformation : session -> transID -> unit
(** [remove_transformation s id] removes the transformation [id]
    from the session [s] *)

val save_session : string -> session -> unit
(** [save_session f s] Save the session [s] in file [f] *)

val load_session : string -> session
(** [load_session f] load a session from a file [f]; all the tasks are
    initialised to None *)
