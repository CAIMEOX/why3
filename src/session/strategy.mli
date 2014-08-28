
open Why3

(** {2 User-defined strategies} *)

(** A strategy is defined by a program declared under a simple
      assembly-like form: instructions are indexed by integers
      starting from 0 (the initial instruction counter). An
      instruction is either
      1) a call to a prover, with given time and mem limits
      . on success, the program execution ends
      . on any other result, the program execution continues on the next index
      2) a application of a transformation
      . on success, the execution continues to a explicitly given index
      . on failure, execution continues on the next index
      3) a goto instruction.

      the execution halts when reaching a non-existing state
  *)

type instruction =
  | Icall_prover of Whyconf.prover * int * int (** timelimit, memlimit *)
  | Itransform of string * int (** successor state on success *)
  | Igoto of int (** goto state *)

type t = instruction array


