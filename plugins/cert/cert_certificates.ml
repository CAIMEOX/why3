open Format

open Why3
open Decl
open Term
open Ident

open Cert_abstract

type dir = Left | Right
type path = dir list

(** We equip each transformation application with a certificate indicating
    why the resulting list of tasks is implying the initial task *)

type ('a, 'b) cert = (* 'a is used to designate an hypothesis, 'b is used for terms *)
  (* Replaying a certif <cert> against a ctask <cta> will be denoted <cert ⇓ cta>.
     For more details, take a look at the OCaml implementation <Cert_verif_caml.ccheck>. *)
  | Nc
  (* Makes verification fail : use it as a placeholder *)
  | Hole of ident
  (* Hole ct ⇓ (Γ ⊢ Δ) ≜  [ct : Γ ⊢ Δ] *)
  | Cut of 'a * 'b * ('a, 'b) cert * ('a, 'b) cert
  (* Cut (I, A, c₁, c₂) ⇓ (Γ ⊢ Δ) ≜  (c₁ ⇓ (Γ ⊢ Δ, I : A))  @  (c₂ ⇓ (Γ, I : A ⊢ Δ)) *)
  | Let of 'b * 'a * ('a, 'b) cert
  (* Let (x, I, c) ⇓ t ≜  c ⇓ t[x ← I(t)] *)
  (* Or : x can be used in c as the formula identified by I in t *)
  | Rename of 'a * 'a * ('a, 'b) cert
  (* Rename (I₁, I₂, c) ⇓  (Γ, I₁ : A ⊢ Δ) ≜ c ⇓ (Γ, I₂ : A ⊢ Δ)*)
  (* Rename (I₁, I₂, c) ⇓  (Γ ⊢ Δ, I₁ : A) ≜ c ⇓ (Γ ⊢ Δ, I₂ : A)*)
  | Axiom of 'a * 'a
  (* Axiom (i1, i2) ⇓ (Γ, i1 : A ⊢ Δ, i2 : A) ≜  [] *)
  (* Axiom (i1, i2) ⇓ (Γ, i2 : A ⊢ Δ, i1 : A) ≜  [] *)
  | Trivial of 'a
  (* Trivial I ⇓ (Γ, I : false ⊢ Δ) ≜  [] *)
  (* Trivial I ⇓ (Γ ⊢ Δ, I : true ) ≜  [] *)
  | Split of 'a * ('a, 'b) cert * ('a, 'b) cert
  (* Split (I, c₁, c₂) ⇓ (Γ, I : A ∨ B ⊢ Δ) ≜  (c₁ ⇓ (Γ, I : A ⊢ Δ))  @  (c₂ ⇓ (Γ, I : B ⊢ Δ)) *)
  (* Split (I, c₁, c₂) ⇓ (Γ ⊢ Δ, I : A ∧ B) ≜  (c₁ ⇓ (Γ ⊢ Δ, I : A))  @  (c₂ ⇓ (Γ ⊢ Δ, I : B)) *)
  | Unfold of 'a * ('a, 'b) cert
  (* Unfold (I, c) ⇓ (Γ, I : A ↔ B ⊢ Δ) ≜  c ⇓ (Γ, I : (A → B) ∧ (B → A) ⊢ Δ) *)
  (* Unfold (I, c) ⇓ (Γ ⊢ Δ, I : A ↔ B) ≜  c ⇓ (Γ ⊢ Δ, I : (A → B) ∧ (B → A)) *)
  (* Unfold (I, c) ⇓ (Γ, I : A → B ⊢ Δ) ≜  c ⇓ (Γ, I : ¬A ∨ B ⊢ Δ)*)
  (* Unfold (I, c) ⇓ (Γ ⊢ Δ, I : A → B) ≜  c ⇓ (Γ ⊢ Δ, I : ¬A ∨ B)*)
  | Swap of 'a * ('a, 'b) cert
  (* Swap (I, c) ⇓ (Γ, I : ¬A ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ, I : A)  *)
  (* Swap (I, c) ⇓ (Γ, I : A ⊢ Δ ) ≜  c ⇓ (Γ ⊢ Δ, I : ¬A) *)
  (* Swap (I, c) ⇓ (Γ ⊢ Δ, I : A ) ≜  c ⇓ (Γ, I : ¬A ⊢ Δ) *)
  (* Swap (I, c) ⇓ (Γ ⊢ Δ, I : ¬A) ≜  c ⇓ (Γ, I : A ⊢ Δ)  *)
  | Destruct of 'a * 'a * 'a * ('a, 'b) cert
  (* Destruct (I, J₁, J₂, c) ⇓ (Γ, I : A ∧ B ⊢ Δ) ≜  c ⇓ (Γ, J₁ : A, J₂ : B ⊢ Δ) *)
  (* Destruct (I, J₁, J₂, c) ⇓ (Γ ⊢ Δ, I : A ∨ B) ≜  c ⇓ (Γ ⊢ Δ, J₁ : A, J₂ : B) *)
  | Construct of 'a * 'a * 'a * ('a, 'b) cert
  (* Construct (I₁, I₂, J, c) ⇓ (Γ, I₁ : A, I₂ : B ⊢ Δ) ≜  c ⇓ (Γ, J : A ∧ B ⊢ Δ) *)
  (* Construct (I₁, I₂, J, c) ⇓ (Γ ⊢ Δ, I₁ : A, I₂ : B) ≜  c ⇓ (Γ ⊢ Δ, J : A ∧ B) *)
  | Weakening of 'a * ('a, 'b) cert
  (* Weakening (I, c) ⇓ (Γ ⊢ Δ, I : A) ≜  c ⇓ (Γ ⊢ Δ) *)
  (* Weakening (I, c) ⇓ (Γ, I : A ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ) *)
  | IntroQuant of 'a * ident * ('a, 'b) cert
  (* IntroQuant (I, y, c) ⇓ (Γ, I : ∃ x. P x ⊢ Δ) ≜  c ⇓ (Γ, I : P y ⊢ Δ) (y fresh) *)
  (* IntroQuant (I, y, c) ⇓ (Γ ⊢ Δ, I : ∀ x. P x) ≜  c ⇓ (Γ ⊢ Δ, I : P y) (y fresh) *)
  | InstQuant of 'a * 'a * 'b * ('a, 'b) cert
  (* InstQuant (I, J, t, c) ⇓ (Γ, I : ∀ x. P x ⊢ Δ) ≜  c ⇓ (Γ, I : ∀ x. P x, J : P t ⊢ Δ) *)
  (* InstQuant (I, J, t, c) ⇓ (Γ ⊢ Δ, I : ∃ x. P x) ≜  c ⇓ (Γ ⊢ Δ, I : ∃ x. P x, J : P t) *)
  | Rewrite of 'a * 'a * path * bool * ('a, 'b) cert list
  (* Rewrite (I, J, path, rev, lc) ⇓ Seq is defined as follows :
     it tries to rewrite in <I> an equality that is in <J>, following the path <path>,
     <rev> indicates if it rewrites from left to right or from right to left.
     Since <H> can have premises, those are then matched against the certificates <lc> *)

type visible_cert = (prsymbol, term) cert
type abstract_cert = (ident, cterm) cert

type ctrans = visible_cert ctransformation

type ('a, 'b) ecert = (* elaborated certificates, 'a is used to designate an hypothesis,
 'b is used for terms, 'c is used for tasks *)
  | EHole of ident
  (* EHole ⇓ (Γ ⊢ Δ) ≜  [Γ ⊢ Δ] *)
  | ECut of 'a * 'b * ('a, 'b) ecert * ('a, 'b) ecert
  (* ECut (I, A, c₁, c₂) ⇓ (Γ ⊢ Δ) ≜  (c₁ ⇓ (Γ ⊢ Δ, I : A))  @  (c₂ ⇓ (Γ, I : A ⊢ Δ)) *)
  | ELet of 'b * 'b * ('a, 'b) ecert
  (* ELet (x, y, c) ⇓ t ≜  c ⇓ t[x ←  y] *)
  | EAxiom of 'b * 'a * 'a
  (* EAxiom (A, i1, i2) ⇓ (Γ, i1 : A ⊢ Δ, i2 : A) ≜  [] *)
  (* Notice that there is only one rule *)
  | ETrivial of bool * 'a
  (* ETrivial (false, I) ⇓ (Γ, I : false ⊢ Δ) ≜  [] *)
  (* ETrivial (true, I) ⇓ (Γ ⊢ Δ, I : true ) ≜  [] *)
  | ERename of bool * 'b * 'a * 'a * ('a, 'b) ecert
  (* ERename (false, A, I₁, I₂, c) ⇓  (Γ, I₁ : A ⊢ Δ) ≜ c ⇓ (Γ, I₂ : A ⊢ Δ)*)
  (* ERename (true, A, I₁, I₂, c) ⇓  (Γ ⊢ Δ, I₁ : A) ≜ c ⇓ (Γ ⊢ Δ, I₂ : A)*)
  | ESplit of bool * 'b * 'b * 'a * ('a, 'b) ecert * ('a, 'b) ecert
  (* ESplit (false, A, B, I, c₁, c₂) ⇓ (Γ, I : A ∨ B ⊢ Δ) ≜  (c₁ ⇓ (Γ, I : A ⊢ Δ))  @  (c₂ ⇓ (Γ, I : B ⊢ Δ)) *)
  (* ESplit (true, A, B, I, c₁, c₂) ⇓ (Γ ⊢ Δ, I : A ∧ B) ≜  (c₁ ⇓ (Γ ⊢ Δ, I : A))  @  (c₂ ⇓ (Γ ⊢ Δ, I : B)) *)
  | EUnfoldIff of (bool * 'b * 'b * 'a * ('a, 'b) ecert)
  (* EUnfoldIff (false, A, B, I, c) ⇓ (Γ, I : A ↔ B ⊢ Δ) ≜  c ⇓ (Γ, I : (A → B) ∧ (B → A) ⊢ Δ) *)
  (* EUnfoldIff (true, A, B, I, c) ⇓ (Γ ⊢ Δ, I : A ↔ B) ≜  c ⇓ (Γ ⊢ Δ, I : (A → B) ∧ (B → A)) *)
  | EUnfoldArr of (bool * 'b * 'b * 'a * ('a, 'b) ecert)
  (* EUnfoldArr (false, A, B, I, c) ⇓ (Γ, I : A → B ⊢ Δ) ≜  c ⇓ (Γ, I : ¬A ∨ B ⊢ Δ)*)
  (* EUnfoldArr (true, A, B, I, c) ⇓ (Γ ⊢ Δ, I : A → B) ≜  c ⇓ (Γ ⊢ Δ, I : ¬A ∨ B)*)
  | ESwap of (bool * 'b * 'a * ('a, 'b) ecert)
  (* ESwap (false, A, I, c) ⇓ (Γ, I : A ⊢ Δ ) ≜  c ⇓ (Γ ⊢ Δ, I : ¬A) *)
  (* ESwap (true, A, I, c) ⇓ (Γ ⊢ Δ, I : A ) ≜  c ⇓ (Γ, I : ¬A ⊢ Δ) *)
  | ESwapNeg of (bool * 'b * 'a * ('a, 'b) ecert)
  (* ESwap_neg (false, A, I, c) ⇓ (Γ, I : ¬A ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ, I : A)  *)
  (* ESwap_neg (true, A, I, c) ⇓ (Γ ⊢ Δ, I : ¬A) ≜  c ⇓ (Γ, I : A ⊢ Δ)  *)
  | EDestruct of bool * 'b * 'b * 'a * 'a * 'a * ('a, 'b) ecert
  (* EDestruct (false, A, B, I, J₁, J₂, c) ⇓ (Γ, I : A ∧ B ⊢ Δ) ≜  c ⇓ (Γ, J₁ : A, J₂ : B ⊢ Δ) *)
  (* EDestruct (true, A, B, I, J₁, J₂, c) ⇓ (Γ ⊢ Δ, I : A ∨ B) ≜  c ⇓ (Γ ⊢ Δ, J₁ : A, J₂ : B) *)
  | EConstruct of bool * 'b * 'b * 'a * 'a * 'a * ('a, 'b) ecert
  (* EConstruct (false, A, B, I₁, I₂, J, c) ⇓ (Γ, I₁ : A, I₂ : B ⊢ Δ) ≜  c ⇓ (Γ, J : A ∧ B ⊢ Δ) *)
  (* EConstruct (true, A, B, I₁, I₂, J, c) ⇓ (Γ ⊢ Δ, I₁ : A, I₂ : B) ≜  c ⇓ (Γ ⊢ Δ, J : A ∧ B) *)
  | EWeakening of bool * 'b * 'a * ('a, 'b) ecert
  (* EWeakening (true, A, I, c) ⇓ (Γ ⊢ Δ, I : A) ≜  c ⇓ (Γ ⊢ Δ) *)
  (* EWeakening (false, A, I, c) ⇓ (Γ, I : A ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ) *)
  | EIntroQuant of bool * 'b * 'a * ident * ('a, 'b) ecert
  (* EIntroQuant (false, P, I, y, c) ⇓ (Γ, I : ∃ x. P x ⊢ Δ) ≜  c ⇓ (Γ, I : P y ⊢ Δ) (y fresh) *)
  (* EIntroQuant (true, P, I, y, c) ⇓ (Γ ⊢ Δ, I : ∀ x. P x) ≜  c ⇓ (Γ ⊢ Δ, I : P y) (y fresh) *)
  | EInstQuant of bool * 'b * 'a * 'a * 'b * ('a, 'b) ecert
  (* InstQuant (false, P, I, J, t, c) ⇓ (Γ, I : ∀ x. P x ⊢ Δ) ≜  c ⇓ (Γ, I : ∀ x. P x, J : P t ⊢ Δ) *)
  (* InstQuant (true, P, I, J, t, c) ⇓ (Γ ⊢ Δ, I : ∃ x. P x) ≜  c ⇓ (Γ ⊢ Δ, I : ∃ x. P x, J : P t) *)
  | ERewrite of 'a * 'a * path * bool * ('a, 'b) ecert list
(* Rewrite (I, J, path, rev, lc) ⇓ Seq is defined as follows :
   *    it tries to rewrite in <I> an equality that is in <J>, following the path <path>,
   *    <rev> indicates if it rewrites from left to right or from right to left.
   *    Since <H> can have premises, those are then matched against the certificates <lc> *)

type heavy_ecert = (ident, cterm) ecert
type trimmed_ecert = (ident, cterm) ecert (* without (Rename,Construct) *)
type kernel_ecert = (ident, cterm) ecert (* without (Rename,Construct,Let) *)

(** Printing of <cterm> and <ctask> : for debugging purposes *)

let ip = create_ident_printer []

let pri fmt i =
  fprintf fmt "%s" (id_unique ip i)

let prpr fmt pr =
  pri fmt pr.pr_name

let prd fmt = function
  | Left -> fprintf fmt "Left"
  | Right -> fprintf fmt "Right"

let prle sep pre fmt le =
  let prl = pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt sep) pre in
  fprintf fmt "[%a]" prl le

let rec pcte fmt = function
  | CTbvar lvl -> pp_print_int fmt lvl
  | CTfvar i -> pri fmt i
  | CTapp (f, arg) -> fprintf fmt "%a@ %a" pcte f pcte arg
  | CTbinop (op, t1, t2) ->
      fprintf fmt "(%a %a %a)" pcte t1 pro op pcte t2
  | CTquant (q, ct) -> begin match q with
                       | CTforall -> fprintf fmt "∀. %a" pcte ct
                       | CTexists -> fprintf fmt "∃. %a" pcte ct
                       | CTlambda -> fprintf fmt "λ. %a" pcte ct
                       end
  | CTnot t -> fprintf fmt "(not %a)" pcte t
  | CTtrue -> fprintf fmt "true"
  | CTfalse -> fprintf fmt "false"
and pro fmt = function
  | Tor -> fprintf fmt "\\/"
  | Tand -> fprintf fmt "/\\"
  | Timplies -> fprintf fmt "->"
  | Tiff -> fprintf fmt "<->"

let pte = Pretty.print_term

let po p fmt = function
  | None -> fprintf fmt "None"
  | Some x -> fprintf fmt "%a" p x


let rec print_certif filename cert =
  let oc = open_out filename in
  let fmt = formatter_of_out_channel oc in
  fprintf fmt "%a@." prcertif cert;
  close_out oc
and prcab : type a b. (formatter -> a -> unit) ->
                 (formatter -> b -> unit) ->
                 formatter -> (a, b) cert -> unit
  = fun pra prb fmt c ->
  let prc = prcab pra prb in
  match c with
  | Nc -> fprintf fmt "No_certif"
  | Hole ct -> fprintf fmt "Hole %a" pri ct
  | Cut (i, a, c1, c2) -> fprintf fmt "Cut @[(%a,@ %a,@ %a,@ %a)@]" pra i prb a prc c1 prc c2
  | Let (x, i, c) -> fprintf fmt "Let @[(%a,@ %a,@ %a)@]" prb x pra i prc c
  | Rename (i1, i2, c) -> fprintf fmt "Rename @[(%a,@ %a,@ %a)@]" pra i1 pra i2 prc c
  | Axiom (i1, i2) -> fprintf fmt "Axiom @[(%a,@ %a)@]" pra i1 pra i2
  | Trivial i -> fprintf fmt "Trivial %a" pra i
  | Split (i, c1, c2) -> fprintf fmt "Split @[(%a,@ %a,@ %a)@]" pra i prc c1 prc c2
  | Unfold (i, c) -> fprintf fmt "Unfold @[(%a,@ %a)@]" pra i prc c
  | Swap (i, c) -> fprintf fmt "Swap @[(%a,@ %a)@]" pra i prc c
  | Destruct (i, j1, j2, c) ->
      fprintf fmt "Destruct @[(%a,@ %a,@ %a,@ %a)@]" pra i pra j1 pra j2 prc c
  | Construct (i1, i2, j, c) ->
      fprintf fmt "Construct @[(%a,@ %a,@ %a,@ %a)@]" pra i1 pra i2 pra j prc c
  | Weakening (i, c) -> fprintf fmt "Weakening@ @[(%a,@ %a)@]" pra i prc c
  | IntroQuant (i, y, c) -> fprintf fmt "IntroQuant @[(%a,@ %a,@ %a)@]" pra i pri y prc c
  | InstQuant (i, j, t, c) -> fprintf fmt "InstQuant @[(%a,@ %a,@ %a,@ %a)@]" pra i pra j prb t prc c
  | Rewrite (i, j, path, rev, lc) ->
      fprintf fmt "Rewrite @[(%a,@ %a,@ %a,@ %b,@ %a)@]"
        pra i pra j (prle "; " prd) path rev (prle "; " prc) lc
and prcertif fmt = prcab prpr pte fmt
and prcore_certif fmt = prcab pri pcte fmt

let eprcertif c = eprintf "%a@." prcertif c

let prpos fmt = function
  | true  -> fprintf fmt "GOAL| "
  | false -> fprintf fmt "HYP | "

let prmid fmt mid =
  Mid.iter (fun h (cte, pos) -> fprintf fmt "%a%a : %a\n" prpos pos pri h pcte cte) mid

let pcta fmt cta =
  fprintf fmt "%a\n" prmid cta

let print_ctasks filename lcta =
  let oc = open_out filename in
  let fmt = formatter_of_out_channel oc in
  fprintf fmt "%a@." (prle "==========\n" pcta) lcta;
  close_out oc

let find_ident s h cta =
  match Mid.find_opt h cta with
  | Some x -> x
  | None ->
      fprintf str_formatter "%s : Can't find ident %a in the task" s pri h;
      verif_failed (flush_str_formatter ())

(** Utility functions on certificate, cterm and ctask *)

(* Structural functions on certificates *)
let propagate_cert f fid fte = function
  | (Hole _ | Nc)  as c -> c
  | Axiom (h, g) -> Axiom (fid h, fid g)
  | Trivial i -> Trivial (fid i)
  | Cut (i, a, c1, c2) ->
      let f1 = f c1 in let f2 = f c2 in
      Cut (fid i, fte a, f1, f2)
  | Let (x, i, c) -> Let (fte x, fid i, f c)
  | Rename (i1, i2, c) -> Rename (fid i1, fid i2, f c)
  | Unfold (i, c) -> Unfold (fid i, f c)
  | Split (i, c1, c2) ->
      let f1 = f c1 in let f2 = f c2 in
      Split (fid i, f1, f2)
  | Swap (i, c) -> Swap (fid i, f c)
  | Destruct (i, j1, j2, c) -> Destruct (fid i, fid j1, fid j2, f c)
  | Construct (i1, i2, j, c) -> Construct (fid i1, fid i2, fid j, f c)
  | Weakening (i, c) -> Weakening (fid i, f c)
  | IntroQuant (i, y, c) -> IntroQuant (fid i, y, f c)
  | InstQuant (i, j, t, c) -> InstQuant (fid i, fid j, fte t, f c)
  | Rewrite (i, j, path, rev, lc) -> Rewrite (fid i, fid j, path, rev, List.map f lc)

let rec fill map = function
  | Hole x -> Mid.find x map
  | c -> propagate_cert (fill map) (fun t -> t) (fun t -> t) c

let flatten_uniq l =
  let s = Sid.empty in
  let add acc v = if Sid.mem v s then acc else v::acc in
  let add_list acc nl = List.fold_left add acc nl in
  let add_list_list acc nll = List.fold_left add_list acc nll in
  List.rev (add_list_list [] l)

let (|>>>) (v1, c1) lcv2 =
  let lv2, lc2 = List.split lcv2 in
  assert (List.length v1 = List.length lv2);
  let lvc1 = List.combine v1 lc2 in
  let map = List.fold_left (fun map (v, c) -> Mid.add v c map) Mid.empty lvc1 in
  flatten_uniq lv2, fill map c1

let rec iterate n v = if n = 0 then [] else v :: iterate (n-1) v

let (|>>) (v1, c1) (v2, c2) =
  let n = List.length v1 in
  let lcv2 = iterate n (v2, c2)in
  (v1, c1) |>>> lcv2

let propagate_ecert f fid ft = function
  | EHole _ as c -> c
  | ECut (i, a, c1, c2) ->
      let f1 = f c1 in let f2 = f c2 in
      ECut (fid i, ft a, f1, f2)
  | ELet (x, y, c) -> ELet (ft x, ft y, f c)
  | ERename (g, a, i1, i2, c) -> ERename (g, ft a, fid i1, fid i2, f c)
  | EAxiom (a, i1, i2) -> EAxiom (ft a, fid i1, fid i2)
  | ETrivial (g, i) -> ETrivial (g, fid i)
  | ESplit (g, a, b, i, c1, c2) ->
      let f1 = f c1 in let f2 = f c2 in
      ESplit (g, ft a, ft b, fid i, f1, f2)
  | EUnfoldIff (g, a, b, i, c) -> EUnfoldIff (g, ft a, ft b, fid i, f c)
  | EUnfoldArr (g, a, b, i, c) -> EUnfoldArr (g, ft a, ft b, fid i, f c)
  | ESwap (g, a, i, c) -> ESwap (g, ft a, fid i, f c)
  | ESwapNeg (g, a, i, c) -> ESwapNeg (g, ft a, fid i, f c)
  | EDestruct (g, a, b, i, j1, j2, c) -> EDestruct (g, ft a, ft b, fid i, fid j1, fid j2, f c)
  | EConstruct (g, a, b, i1, i2, j, c) -> EConstruct (g, ft a, ft b, fid i1, fid i2, fid j, f c)
  | EWeakening (g, a, i, c) -> EWeakening (g, ft a, fid i, f c)
  | EIntroQuant (g, p, i, y, c) -> EIntroQuant (g, ft p, fid i, y, f c)
  | EInstQuant (g, p, i, j, t, c) -> EInstQuant (g, ft p, fid i, fid j, ft t, f c)
  | ERewrite (i, j, path, rev, lc) -> ERewrite (fid i, fid j, path, rev, List.map f lc)


(* Equality *)
let rec cterm_equal t1 t2 = match t1, t2 with
  | CTbvar lvl1, CTbvar lvl2 -> lvl1 = lvl2
  | CTfvar i1, CTfvar i2 -> id_equal i1 i2
  | CTapp (tl1, tr1), CTapp (tl2, tr2) ->
      cterm_equal tl1 tl2 && cterm_equal tr1 tr2
  | CTbinop (op1, tl1, tr1), CTbinop (op2, tl2, tr2) ->
      op1 = op2 && cterm_equal tl1 tl2 && cterm_equal tr1 tr2
  | CTquant (q1, t1), CTquant (q2, t2) when q1 = q2 -> cterm_equal t1 t2
  | CTtrue, CTtrue | CTfalse, CTfalse -> true
  | CTnot t1, CTnot t2 -> cterm_equal t1 t2
  | _ -> false

let cterm_pos_equal (t1, p1) (t2, p2) =
  cterm_equal t1 t2 && p1 = p2

let ctask_equal cta1 cta2 = Mid.equal cterm_pos_equal cta1 cta2

(* Bound variable substitution *)
let rec ct_bv_subst k u t = match t with
  | CTbvar i -> if i = k then u else t
  | CTfvar _ -> t
  | CTapp (t1, t2) ->
      let nt1 = ct_bv_subst k u t1 in
      let nt2 = ct_bv_subst k u t2 in
      CTapp (nt1, nt2)
  | CTbinop (op, t1, t2) ->
      let nt1 = ct_bv_subst k u t1 in
      let nt2 = ct_bv_subst k u t2 in
      CTbinop (op, nt1, nt2)
  | CTquant (q, t) ->
      let nt = ct_bv_subst (k+1) u t in
      CTquant (q, nt)
  | CTnot t -> CTnot (ct_bv_subst k u t)
  | CTtrue -> CTtrue
  | CTfalse -> CTfalse

let ct_open t u = ct_bv_subst 0 u t

(* Checks if the term is locally closed *)
let locally_closed =
  let di = id_register (id_fresh "dummy_locally_closed_ident") in
  let rec term = function
    | CTbvar _ -> false
    | CTapp (t1, t2)
    | CTbinop (_, t1, t2) -> term t1 && term t2
    | CTquant (_, t) -> term (ct_open t (CTfvar di))
    | CTnot t -> term t
    | CTfvar _ | CTtrue | CTfalse -> true
  in
  term

(* Free variable substitution *)
let rec ct_fv_subst z u t = match t with
  | CTfvar x -> if id_equal z x then u else t
  | CTapp (t1, t2) ->
      let nt1 = ct_fv_subst z u t1 in
      let nt2 = ct_fv_subst z u t2 in
      CTapp (nt1, nt2)
  | CTbinop (op, t1, t2) ->
      let nt1 = ct_fv_subst z u t1 in
      let nt2 = ct_fv_subst z u t2 in
      CTbinop (op, nt1, nt2)
  | CTquant (q, t) ->
      let nt = ct_fv_subst z u t in
      CTquant (q, nt)
  | CTnot t -> CTnot (ct_fv_subst z u t)
  | CTbvar _ | CTtrue | CTfalse -> t

let ct_subst ct m =
  Mid.fold ct_fv_subst ct m

(* Variable closing *)
let rec ct_fv_close x k t = match t with
  | CTbvar _ | CTtrue | CTfalse-> t
  | CTfvar y -> if id_equal x y then CTbvar k else t
  | CTnot t -> CTnot (ct_fv_close x k t)
  | CTapp (t1, t2) ->
      let nt1 = ct_fv_close x k t1 in
      let nt2 = ct_fv_close x k t2 in
      CTapp (nt1, nt2)
  | CTbinop (op, t1, t2) ->
      let nt1 = ct_fv_close x k t1 in
      let nt2 = ct_fv_close x k t2 in
      CTbinop (op, nt1, nt2)
  | CTquant (q, t) -> CTquant (q, ct_fv_close x (k+1) t)

let ct_close x t = ct_fv_close x 0 t

(* Find free variable with respect to a term *)
let rec mem_cont x t cont = match t with
  | CTfvar y -> cont (id_equal x y)
  | CTapp (t1, t2)
  | CTbinop (_, t1, t2) ->
      mem_cont x t1 (fun m1 ->
      mem_cont x t2 (fun m2 ->
      cont (m1 || m2)))
  | CTquant (_, t)
  | CTnot t -> mem_cont x t cont
  | CTbvar _ | CTtrue | CTfalse -> cont false

let mem x t = mem_cont x t (fun x -> x)


(* Separates hypotheses and goals *)
let split_cta cta =
  let open Mid in
  fold (fun h (ct, pos) (mh, mg) ->
      if pos then mh, add h (ct, pos) mg
      else add h (ct, pos) mh, mg)
    cta (empty, empty)

(* Creates a new ctask with the same hypotheses but sets the goal with the second argument *)
let set_goal : ctask -> cterm -> ctask = fun cta ->
  let mh, mg = split_cta cta in
  let hg, _ = Mid.choose mg in
  fun ct -> Mid.add hg (ct, true) mh

let rec abstract_types (c : visible_cert) : abstract_cert =
  propagate_cert abstract_types (fun pr -> pr.pr_name) abstract_term c

exception Elaboration_failed of string

let elab_failed s = raise (Elaboration_failed s)

module Hashid = Hashtbl.Make(struct type t = ident let equal = id_equal let hash = id_hash end)


let elaborate (init_ct : ctask) (res_ct : ctask list) (c : abstract_cert) : heavy_ecert =
  (* let res_ct = Stream.of_list res_ct in *)
  (* let tbl = Hashid.create 17 in *)
  let rec elab cta c =
  match c with
  | Nc -> elab_failed "No certificates"
  | Hole _ -> c
  (* TODO : match cta against nct and update tbl accordingly *)
  (* let nct = Stream.next res_ct inc *)
  (* EHole nct *)
  | Axiom (i1, i2) ->
      let a, posi2 = find_ident "Axiom" i2 cta in
      let i1, i2 = if posi2 then i1, i2 else i2, i1 in
      EAxiom (a, i1, i2)
  | Trivial i ->
      let _, pos = find_ident "Trivial" i cta in
      ETrivial (pos, i)
  | Rename (i1, i2, c) ->
      let a, pos = find_ident "Rename" i1 cta in
      let cta = Mid.remove i1 cta
                |> Mid.add i2 (a, pos) in
      let c = elab cta c in
      ERename (pos, a, i1, i2, c)
  | Cut (i, a, c1, c2) ->
      let cta1 = Mid.add i (a, true) cta in
      let cta2 = Mid.add i (a, false) cta in
      let c1 = elab cta1 c1 in
      let c2 = elab cta2 c2 in
      ECut (i, a, c1, c2)
  | Let (x, i, c) ->
      let y, _ = find_ident "Let" i cta in
      ELet (x, y, elab cta c)
  | Split (i, c1, c2) ->
      let t, pos = find_ident "Split" i cta in
      let t1, t2 = match t, pos with
        | CTbinop (Tand, t1, t2), true | CTbinop (Tor, t1, t2), false -> t1, t2
        | _ -> elab_failed "Not splittable" in
      let cta1 = Mid.add i (t1, pos) cta in
      let cta2 = Mid.add i (t2, pos) cta in
      let c1 = elab cta1 c1 in
      let c2 = elab cta2 c2 in
      ESplit (pos, t1, t2, i, c1, c2)
  | Unfold (i, c) ->
      let t, pos = find_ident "Unfold" i cta in
      let iff, cta, t1, t2 = match t with
        | CTbinop (Tiff, t1, t2) ->
            let imp_pos = CTbinop (Timplies, t1, t2) in
            let imp_neg = CTbinop (Timplies, t2, t1) in
            let unfolded_iff = CTbinop (Tand, imp_pos, imp_neg), pos in
            true, Mid.add i unfolded_iff cta, t1, t2
        | CTbinop (Timplies, t1, t2) ->
            let unfolded_imp = CTbinop (Tor, CTnot t1, t2), pos in
            false, Mid.add i unfolded_imp cta, t1, t2
        | _ -> Format.eprintf "@[%a@]@." pcte t;
               elab_failed "Nothing to unfold" in
      let pack = pos, t1, t2, i, elab cta c in
      if iff
      then EUnfoldIff pack
      else EUnfoldArr pack
  | Swap (i, c) ->
      let t, pos = find_ident "Swap" i cta in
      let neg, underlying_t, neg_t = match t with
        | CTnot t -> true, t, t
        | _ -> false, t, CTnot t in
      let cta = Mid.add i (neg_t, not pos) cta in
      let pack = pos, underlying_t, i, elab cta c in
      if neg
      then ESwapNeg pack
      else ESwap pack
  | Destruct (i, j1, j2, c) ->
      let t, pos = find_ident "Destruct" i cta in
      let t1, t2 = match t, pos with
        | CTbinop (Tand, t1, t2), false | CTbinop (Tor, t1, t2), true -> t1, t2
        | _ -> elab_failed "Nothing to destruct" in
      let cta = Mid.remove i cta
                |> Mid.add j1 (t1, pos)
                |> Mid.add j2 (t2, pos) in
      EDestruct (pos, t1, t2, i, j1, j2, elab cta c)
  | Construct (i1, i2, j, c) ->
      let t1, pos1 = find_ident "Construct1" i1 cta in
      let t2, pos2 = find_ident "Construct2" i2 cta in
      assert (pos1 = pos2);
      let t = if pos1 then CTbinop (Tor, t1, t2) else CTbinop (Tand, t1, t2) in
      let cta = Mid.remove i1 cta
                |> Mid.remove i2
                |> Mid.add j (t, pos1) in
      EConstruct (pos1, t1, t2, i1, i2, j, elab cta c)
  | Weakening (i, c) ->
      let t, pos = find_ident "Weakening" i cta in
      let cta = Mid.remove i cta in
      EWeakening (pos, t, i, elab cta c)
  | IntroQuant (i, y, c) ->
      let t, pos = find_ident "IntroQuant" i cta in
      let t = match t, pos with
        | CTquant (CTforall, t), true | CTquant (CTexists, t), false -> t
        | _ -> elab_failed "Nothing to introduce" in
      let cta = Mid.add i (ct_open t (CTfvar y), pos) cta in
      EIntroQuant (pos, CTquant (CTlambda, t), i, y, elab cta c)
  | InstQuant (i, j, t_inst, c) ->
      let t, pos = find_ident "InstQuant" i cta in
      let t = match t, pos with
        | CTquant (CTforall, t), false | CTquant (CTexists, t), true -> t
        | _ -> elab_failed "trying to instantiate a non-quantified hypothesis" in
      let cta = Mid.add j (ct_open t t_inst, pos) cta in
      EInstQuant (pos, CTquant (CTlambda, t), i, j, t_inst, elab cta c)
  | Rewrite _ -> elab_failed "TODO : Rewrite"
  (* TODO *)
  (* let lcta = check_rewrite cta rev j i [] path in
   * List.map2 ccheck lc lcta |> List.concat *)
  in
  elab init_ct c

let eaxiom g a i j =
  if g then EAxiom (a, i, j)
  else EAxiom (a, j, i)

let erename g a i1 i2 c =
  let c_open = EWeakening (g, a, i1, c) in
  let c_closed = eaxiom (not g) a i1 i2 in
  let c1, c2 = if g
               then c_open, c_closed
               else c_closed, c_open in
  ECut (i2, a, c1, c2)

let rec trim_certif (c : heavy_ecert) : trimmed_ecert =
  match c with
  | ERename (g, a, i1, i2, c) ->
      erename g a i1 i2 c
  | EConstruct (g, a, b, i1, i2, j, c) ->
      let c = trim_certif c in
      let i1' = id_register (id_fresh "i1") in
      let i2' = id_register (id_fresh "i2") in
      erename g a i1 i1' (
          erename g b i2 i2' (
              let c_open = EWeakening (g, a, i1', EWeakening (g, b, i2', c)) in
              let c_closed = ESplit (not g, a, b, j,
                                     eaxiom (not g) a i1' j,
                                     eaxiom (not g) b i2' j) in
              let c1, c2, cut = if g
                                then c_open, c_closed, CTbinop (Tor, a, b)
                                else c_closed, c_open, CTbinop (Tand, a, b) in
              ECut (j, cut, c1, c2)))
  | _ -> propagate_ecert trim_certif (fun t -> t) (fun i -> i) c

let rec eliminate_let (m : cterm Mid.t) (c : trimmed_ecert) : kernel_ecert =
  match c with
    | ELet (x, y, c) ->
        let x = match x with
                | CTfvar id -> id
                | _ -> assert false in
        let m = Mid.add x y m in
        eliminate_let m c
    | ECut (i, a, c1, c2) ->
        let c1 = eliminate_let m c1 in
        let c2 = eliminate_let m c2 in
        let a = ct_subst m a in
        ECut (i, a, c1, c2)
    | _ -> propagate_ecert (eliminate_let m) (fun t -> t) (fun i -> i) c

let make_core init_ct res_ct c =
  (* Format.eprintf "%a@." prcertif c; *)
  abstract_types c
  |> elaborate init_ct res_ct
  |> trim_certif
  |> eliminate_let Mid.empty
