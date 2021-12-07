open Why3
open Decl
open Term
open Ty
open Ident
open Format

open Cert_syntax

type sc =
  | Nc
  | Hole of cterm ctask
  | Assert of prsymbol * term * sc * sc
  | Let of prsymbol * (bool -> term -> sc)
  | Axiom of prsymbol * prsymbol
  | Trivial of prsymbol
  | EqSym of prsymbol * sc
  | EqTrans of prsymbol * prsymbol * prsymbol * sc
  | Unfold of prsymbol * sc
  | Fold of prsymbol * sc
  | Split of prsymbol * sc * sc
  | Destruct of prsymbol * prsymbol * prsymbol * sc
  | Swap of prsymbol * sc
  | Clear of prsymbol * sc
  | Forget of lsymbol * sc
  | Duplicate of prsymbol * prsymbol * sc
  | IntroQuant of prsymbol * lsymbol * sc
  | InstQuant of prsymbol * prsymbol * term * sc
  | IntroType of prsymbol * tysymbol list * sc
  | InstType of prsymbol * prsymbol * ty list * sc
  | Rewrite of prsymbol * prsymbol * sc
  | Induction of prsymbol * prsymbol * prsymbol * prsymbol *
                   term * term * sc * sc
  | Conv of prsymbol * term * sc

type scert = int * (sc list -> sc)

type 'a args = Z : sc args | Succ : 'a args -> (sc -> 'a) args

val lambda1 : (scert -> scert) -> scert
val lambda2 : (scert -> scert -> scert) -> scert
val lambdan : int -> (scert list -> scert) -> scert

val ( +++ ) : scert -> scert list -> scert
val ( ++ ) : scert -> scert -> scert

val letc : int -> prsymbol -> (scert list -> bool -> term -> scert) -> scert
val nc : scert
val idc : scert
val assertion : prsymbol -> term -> scert
val axiom : prsymbol -> prsymbol -> scert
val trivial : prsymbol -> scert
val eqsym : prsymbol -> scert
val eqtrans : prsymbol -> prsymbol -> prsymbol -> scert
val unfold : prsymbol -> scert
val fold : prsymbol -> scert
val split : prsymbol -> scert
val destruct : prsymbol -> prsymbol -> prsymbol -> scert
val swap : prsymbol -> scert
val clear : prsymbol -> scert
val forget : lsymbol -> scert
val duplicate : prsymbol -> prsymbol -> scert
val introquant : prsymbol -> lsymbol -> scert
val instquant : prsymbol -> prsymbol -> term -> scert
val introtype : prsymbol -> tysymbol list -> scert
val insttype : prsymbol -> prsymbol -> ty list -> scert
val rewrite : prsymbol -> prsymbol -> scert
val induction :
  prsymbol -> prsymbol -> prsymbol -> prsymbol -> term -> term -> scert
val conv : prsymbol -> term -> scert
val create_eqrefl : prsymbol -> term -> scert
val rename : prsymbol -> prsymbol -> scert
val dir : bool -> prsymbol -> scert
val construct : prsymbol -> prsymbol -> prsymbol -> scert
val iffsym_hyp : prsymbol -> scert

type ctrans = scert ctransformation

type ('ts, 'v, 'ty, 'h, 't) kc =
  | KHole of cterm ctask
  | KClear of bool * 't * 'h * ('ts, 'v, 'ty, 'h, 't) kc
  | KDuplicate of bool * 't * 'h * 'h * ('ts, 'v, 'ty, 'h, 't) kc
  | KForget of 'v * ('ts, 'v, 'ty, 'h, 't) kc
  | KAssert of 'h * 't * ('ts, 'v, 'ty, 'h, 't) kc * ('ts, 'v, 'ty, 'h, 't) kc
  | KAxiom of 't * 'h * 'h
  | KTrivial of bool * 'h
  | KSwap of (bool * 't * 'h * ('ts, 'v, 'ty, 'h, 't) kc)
  | KSwapNegate of (bool * 't * 'h * ('ts, 'v, 'ty, 'h, 't) kc)
  | KUnfoldIff of (bool * 't * 't * 'h * ('ts, 'v, 'ty, 'h, 't) kc)
  | KUnfoldArr of (bool * 't * 't * 'h * ('ts, 'v, 'ty, 'h, 't) kc)
  | KFoldIff of (bool * 't * 't * 'h * ('ts, 'v, 'ty, 'h, 't) kc)
  | KFoldArr of (bool * 't * 't * 'h * ('ts, 'v, 'ty, 'h, 't) kc)
  | KSplit of bool * 't * 't * 'h * ('ts, 'v, 'ty, 'h, 't) kc *
                ('ts, 'v, 'ty, 'h, 't) kc
  | KDestruct of bool * 't * 't * 'h * 'h * 'h * ('ts, 'v, 'ty, 'h, 't) kc
  | KIntroQuant of bool * 'ty * 't * 'h * 'v * ('ts, 'v, 'ty, 'h, 't) kc
  | KInstQuant of bool * 'ty * 't * 'h * 'h * 't * ('ts, 'v, 'ty, 'h, 't) kc
  | KIntroType of 't * 'h * 'ts list * ('ts, 'v, 'ty, 'h, 't) kc
  | KInstType of 't * 'h * 'h * 'ty list * ('ts, 'v, 'ty, 'h, 't) kc
  | KEqRefl of 'ty * 't * 'h
  | KEqSym of bool * 'ty * 't * 't * 'h * ('ts, 'v, 'ty, 'h, 't) kc
  | KEqTrans of 'ty * 't * 't * 't * 'h * 'h * 'h * ('ts, 'v, 'ty, 'h, 't) kc
  | KRewrite of bool * 't option * 'ty * 't * 't * 't * 'h * 'h *
                  ('ts, 'v, 'ty, 'h, 't) kc
  | KInduction of 'h * 'h * 'h * 'h * 't * 't * 't *
                    ('ts, 'v, 'ty, 'h, 't) kc * ('ts, 'v, 'ty, 'h, 't) kc
  | KConv of bool * 't * 't * 'h * ('ts, 'v, 'ty, 'h, 't) kc

type wkc = (tysymbol, lsymbol, ty option, prsymbol, term) kc
type kcert = (ident, ident, ctype, ident, cterm) kc

val print_certif : string -> scert -> unit
val prcertif : formatter -> scert -> unit
val eprcertif : scert -> unit

val make_kernel_cert :
  term ctask -> cterm ctask list -> scert -> kcert
