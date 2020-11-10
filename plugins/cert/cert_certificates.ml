open Why3
open Decl
open Term
open Ident
open Format

open Cert_abstract

(** We equip each transformation application with a certificate indicating
    why the resulting list of tasks is implying the initial task *)

type ('I, 't) cert =
  (* 'I is used to designate an hypothesis, 't is used for terms *)
  (* Replaying a certif <cert> against a ctask <cta> will be denoted <cert ⇓ cta>.
     For more details, take a look at the OCaml implementation <Cert_verif_caml.ccheck>. *)
  | Nc
  (* Makes verification fail : use it as a placeholder *)
  | Hole of ident
  (* Hole ct ⇓ (Γ ⊢ Δ) ≜  ct refers to Γ ⊢ Δ *)
  | Cut of 'I * 't * ('I, 't) cert * ('I, 't) cert
  (* Cut (I, t, c₁, c₂) ⇓ (Σ | Γ ⊢ Δ) ≜
         c₁ ⇓ (Σ | Γ ⊢ Δ, I : t)
     and c₂ ⇓ (Σ | Γ, I : t ⊢ Δ)
     and Σ ⊩ t : bool
   *)
  | Let of 't * 'I * ('I, 't) cert
  (* Let (x, I, c) ⇓ t ≜  c ⇓ t[x ← I(t)] *)
  (* Or : x can be used in c as the formula identified by I in t *)
  | Rename of 'I * 'I * ('I, 't) cert
  (* Rename (I₁, I₂, c) ⇓  (Γ, I₁ : A ⊢ Δ) ≜ c ⇓ (Γ, I₂ : A ⊢ Δ)*)
  (* Rename (I₁, I₂, c) ⇓  (Γ ⊢ Δ, I₁ : A) ≜ c ⇓ (Γ ⊢ Δ, I₂ : A)*)
  | Axiom of 'I * 'I
  (* Axiom (i1, i2) ⇓ (Γ, i1 : A ⊢ Δ, i2 : A) *)
  (* Axiom (i1, i2) ⇓ (Γ, i2 : A ⊢ Δ, i1 : A) *)
  | Trivial of 'I
  (* Trivial I ⇓ (Γ, I : false ⊢ Δ) *)
  (* Trivial I ⇓ (Γ ⊢ Δ, I : true ) *)
  | Unfold of 'I * ('I, 't) cert
  (* Unfold (I, c) ⇓ (Γ, I : A ↔ B ⊢ Δ) ≜  c ⇓ (Γ, I : (A → B) ∧ (B → A) ⊢ Δ) *)
  (* Unfold (I, c) ⇓ (Γ ⊢ Δ, I : A ↔ B) ≜  c ⇓ (Γ ⊢ Δ, I : (A → B) ∧ (B → A)) *)
  (* Unfold (I, c) ⇓ (Γ, I : A → B ⊢ Δ) ≜  c ⇓ (Γ, I : ¬A ∨ B ⊢ Δ)*)
  (* Unfold (I, c) ⇓ (Γ ⊢ Δ, I : A → B) ≜  c ⇓ (Γ ⊢ Δ, I : ¬A ∨ B)*)
  | Fold of 'I * ('I, 't) cert
  (* Fold (I, c) ⇓ (Γ, I : ¬A ∨ B ⊢ Δ) ≜  c ⇓ (Γ, I : A → B ⊢ Δ)*)
  (* Fold (I, c) ⇓ (Γ ⊢ Δ, I : ¬A ∨ B) ≜  c ⇓ (Γ ⊢ Δ, I : A → B)*)
  | Split of 'I * ('I, 't) cert * ('I, 't) cert
  (* Split (I, c₁, c₂) ⇓ (Γ, I : A ∨ B ⊢ Δ) ≜
         c₁ ⇓ (Γ, I : A ⊢ Δ)
     and c₂ ⇓ (Γ, I : B ⊢ Δ) *)
  (* Split (I, c₁, c₂) ⇓ (Γ ⊢ Δ, I : A ∧ B) ≜  (
         c₁ ⇓ (Γ ⊢ Δ, I : A)
     and c₂ ⇓ (Γ ⊢ Δ, I : B) *)
  | Destruct of 'I * 'I * 'I * ('I, 't) cert
  (* Destruct (I, J₁, J₂, c) ⇓ (Γ, I : A ∧ B ⊢ Δ) ≜  c ⇓ (Γ, J₁ : A, J₂ : B ⊢ Δ) *)
  (* Destruct (I, J₁, J₂, c) ⇓ (Γ ⊢ Δ, I : A ∨ B) ≜  c ⇓ (Γ ⊢ Δ, J₁ : A, J₂ : B) *)
  | Construct of 'I * 'I * 'I * ('I, 't) cert
  (* Construct (I₁, I₂, J, c) ⇓ (Γ, I₁ : A, I₂ : B ⊢ Δ) ≜  c ⇓ (Γ, J : A ∧ B ⊢ Δ) *)
  (* Construct (I₁, I₂, J, c) ⇓ (Γ ⊢ Δ, I₁ : A, I₂ : B) ≜  c ⇓ (Γ ⊢ Δ, J : A ∧ B) *)
  | Swap of 'I * ('I, 't) cert
  (* Swap (I, c) ⇓ (Γ, I : ¬A ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ, I : A)  *)
  (* Swap (I, c) ⇓ (Γ, I : A ⊢ Δ ) ≜  c ⇓ (Γ ⊢ Δ, I : ¬A) *)
  (* Swap (I, c) ⇓ (Γ ⊢ Δ, I : A ) ≜  c ⇓ (Γ, I : ¬A ⊢ Δ) *)
  (* Swap (I, c) ⇓ (Γ ⊢ Δ, I : ¬A) ≜  c ⇓ (Γ, I : A ⊢ Δ)  *)
  | Dir of bool * 'I * ('I, 't) cert
  (* Dir (false, I, c) ⇓ (Γ, I : A ∧ B ⊢ Δ) ≜  c ⇓ (Γ, I : A ⊢ Δ) *)
  (* Dir (true, I, c) ⇓ (Γ, I : A ∧ B ⊢ Δ) ≜  c ⇓ (Γ, I : B ⊢ Δ) *)
  (* Dir (false, I, c) ⇓ (Γ ⊢ Δ, I : A ∧ B) ≜  c ⇓ (Γ ⊢ Δ, I : A) *)
  (* Dir (true, I, c) ⇓ (Γ ⊢ Δ, I : A ∧ B) ≜  c ⇓ (Γ ⊢ Δ, I : B) *)
  | Weakening of 'I * ('I, 't) cert
  (* Weakening (I, c) ⇓ (Γ ⊢ Δ, I : A) ≜  c ⇓ (Γ ⊢ Δ) *)
  (* Weakening (I, c) ⇓ (Γ, I : A ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ) *)
  | IntroQuant of 'I * ident * ('I, 't) cert
  (* IntroQuant (I, y, c) ⇓ (Σ | Γ, I : ∃ x : τ. P x ⊢ Δ) ≜
         c ⇓ (Σ, y : τ | Γ, I : P y ⊢ Δ)
     and y ∉  Σ *)
  (* IntroQuant (I, y, c) ⇓ (Σ | Γ ⊢ Δ, I : ∀ x : τ. P x) ≜
         c ⇓ (Σ, y : τ | Γ ⊢ Δ, I : P y)
     and y ∉  Σ *)
  | InstQuant of 'I * 'I * 't * ('I, 't) cert
  (* InstQuant (I, J, t, c) ⇓ (Σ | Γ, I : ∀ x : τ. P x ⊢ Δ) ≜
         c ⇓ (Σ | Γ, I : ∀ x : τ. P x, J : P t ⊢ Δ)
     and Σ ⊩ t : τ *)
  (* InstQuant (I, J, t, c) ⇓ (Σ | Γ ⊢ Δ, I : ∃ x : τ. P x) ≜
         c ⇓ (Σ | Γ ⊢ Δ, I : ∃ x : τ. P x, J : P t)
     and Σ ⊩ t : τ *)
  | Rewrite of 'I * 'I * ('I, 't) cert
  (* Rewrite (I, H, c) ⇓ (Γ, H : a = b ⊢ Δ, I : C[a] ≜  (Γ, H : a = b ⊢ Δ, I : C[b] *)
  (* Rewrite (I, H, c) ⇓ (Γ, H : a = b, I : C[a] ⊢ Δ ≜  (Γ, H : a = b, I : C[b] ⊢ Δ *)

type vcert = (prsymbol, term) cert

type visible_cert = ident list * (prsymbol, term) cert

let nc = [], Nc

type 'a args =
  | Z : vcert args
  | One : (ident -> vcert) args
  | Two : (ident -> ident -> vcert) args
  | List : int -> (ident list -> vcert) args

let rec new_idents n =
  if n = 0 then [] else
    let i = id_register (id_fresh "s") in
    i:: new_idents (n-1)

let lambda : type a. a args -> a -> visible_cert  = fun args f ->
  match args with
  | Z -> [], f
  | One -> let i = id_register (id_fresh "s") in
           [i], f i
  | Two -> let i1 = id_register (id_fresh "s") in
           let i2 = id_register (id_fresh "s") in
           [i1; i2], f i1 i2
  | List n ->
      let il = new_idents n in
      il, f il

let hole () : visible_cert =
  lambda One (fun i -> Hole i)

type abstract_cert = ident list * (ident, cterm) cert

type ctrans = visible_cert ctransformation

type ('a, 'b) ecert =
  (* elaborated certificates :
     ∙ 'a is used to designate an hypothesis
     ∙ 'b is used for terms *)
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
  | EUnfoldIff of (bool * 'b * 'b * 'a * ('a, 'b) ecert)
  (* EUnfoldIff (false, A, B, I, c) ⇓ (Γ, I : A ↔ B ⊢ Δ) ≜  c ⇓ (Γ, I : (A → B) ∧ (B → A) ⊢ Δ) *)
  (* EUnfoldIff (true, A, B, I, c) ⇓ (Γ ⊢ Δ, I : A ↔ B) ≜  c ⇓ (Γ ⊢ Δ, I : (A → B) ∧ (B → A)) *)
  | EUnfoldArr of (bool * 'b * 'b * 'a * ('a, 'b) ecert)
  (* EUnfoldArr (false, A, B, I, c) ⇓ (Γ, I : A → B ⊢ Δ) ≜  c ⇓ (Γ, I : ¬A ∨ B ⊢ Δ)*)
  (* EUnfoldArr (true, A, B, I, c) ⇓ (Γ ⊢ Δ, I : A → B) ≜  c ⇓ (Γ ⊢ Δ, I : ¬A ∨ B)*)
  | EFoldArr of (bool * 'b * 'b * 'a * ('a, 'b) ecert)
  (* EFoldArr (false, A, B, I, c) ⇓ (Γ, I : ¬A ∨ B ⊢ Δ) ≜  c ⇓ (Γ, I : A → B ⊢ Δ)*)
  (* EFoldArr (true, A, B, I, c) ⇓ (Γ ⊢ Δ, I : ¬A ∨ B) ≜  c ⇓ (Γ ⊢ Δ, I : A → B)*)
  | ESplit of bool * 'b * 'b * 'a * ('a, 'b) ecert * ('a, 'b) ecert
  (* ESplit (false, A, B, I, c₁, c₂) ⇓ (Γ, I : A ∨ B ⊢ Δ) ≜  (c₁ ⇓ (Γ, I : A ⊢ Δ))  @  (c₂ ⇓ (Γ, I : B ⊢ Δ)) *)
  (* ESplit (true, A, B, I, c₁, c₂) ⇓ (Γ ⊢ Δ, I : A ∧ B) ≜  (c₁ ⇓ (Γ ⊢ Δ, I : A))  @  (c₂ ⇓ (Γ ⊢ Δ, I : B)) *)
  | EDestruct of bool * 'b * 'b * 'a * 'a * 'a * ('a, 'b) ecert
  (* EDestruct (false, A, B, I, J₁, J₂, c) ⇓ (Γ, I : A ∧ B ⊢ Δ) ≜  c ⇓ (Γ, J₁ : A, J₂ : B ⊢ Δ) *)
  (* EDestruct (true, A, B, I, J₁, J₂, c) ⇓ (Γ ⊢ Δ, I : A ∨ B) ≜  c ⇓ (Γ ⊢ Δ, J₁ : A, J₂ : B) *)
  | EConstruct of bool * 'b * 'b * 'a * 'a * 'a * ('a, 'b) ecert
  (* EConstruct (false, A, B, I₁, I₂, J, c) ⇓ (Γ, I₁ : A, I₂ : B ⊢ Δ) ≜  c ⇓ (Γ, J : A ∧ B ⊢ Δ) *)
  (* EConstruct (true, A, B, I₁, I₂, J, c) ⇓ (Γ ⊢ Δ, I₁ : A, I₂ : B) ≜  c ⇓ (Γ ⊢ Δ, J : A ∧ B) *)
  | ESwap of (bool * 'b * 'a * ('a, 'b) ecert)
  (* ESwap (false, A, I, c) ⇓ (Γ, I : A ⊢ Δ ) ≜  c ⇓ (Γ ⊢ Δ, I : ¬A) *)
  (* ESwap (true, A, I, c) ⇓ (Γ ⊢ Δ, I : A ) ≜  c ⇓ (Γ, I : ¬A ⊢ Δ) *)
  | ESwapNeg of (bool * 'b * 'a * ('a, 'b) ecert)
  (* ESwap_neg (false, A, I, c) ⇓ (Γ, I : ¬A ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ, I : A)  *)
  (* ESwap_neg (true, A, I, c) ⇓ (Γ ⊢ Δ, I : ¬A) ≜  c ⇓ (Γ, I : A ⊢ Δ)  *)
  | EWeakening of bool * 'b * 'a * ('a, 'b) ecert
  (* EWeakening (true, A, I, c) ⇓ (Γ ⊢ Δ, I : A) ≜  c ⇓ (Γ ⊢ Δ) *)
  (* EWeakening (false, A, I, c) ⇓ (Γ, I : A ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ) *)
  | EIntroQuant of bool * 'b * 'a * ident * ('a, 'b) ecert
  (* EIntroQuant (false, P, I, y, c) ⇓ (Γ, I : ∃ x. P x ⊢ Δ) ≜  c ⇓ (Γ, I : P y ⊢ Δ) (y fresh) *)
  (* EIntroQuant (true, P, I, y, c) ⇓ (Γ ⊢ Δ, I : ∀ x. P x) ≜  c ⇓ (Γ ⊢ Δ, I : P y) (y fresh) *)
  | EInstQuant of bool * 'b * 'a * 'a * 'b * ('a, 'b) ecert
  (* InstQuant (false, P, I, J, t, c) ⇓ (Γ, I : ∀ x. P x ⊢ Δ) ≜  c ⇓ (Γ, I : ∀ x. P x, J : P t ⊢ Δ) *)
  (* InstQuant (true, P, I, J, t, c) ⇓ (Γ ⊢ Δ, I : ∃ x. P x) ≜  c ⇓ (Γ ⊢ Δ, I : ∃ x. P x, J : P t) *)
  | ERewrite of bool * ctype * 'b * 'b * 'b * 'a * 'a * ('a, 'b) ecert
  (* ERewrite (true, _, a, b, ctxt, I, H, c) ⇓ (Γ, H : a = b ⊢ Δ, I : ctxt[a] ≜
     (Γ, H : a = b ⊢ Δ, I : ctxt[b] *)
  (* ERewrite (false, _, a, b, ctxt, I, H, c) ⇓ (Γ, H : a = b, I : ctxt[a] ⊢ Δ ≜
     (Γ, H : a = b, I : ctxt[b] ⊢ Δ *)

type heavy_ecert = ident list * (ident, cterm) ecert
type trimmed_ecert = ident list * (ident, cterm) ecert (* without (Rename,Construct) *)
type kernel_ecert = ident list * (ident, cterm) ecert (* without (Rename,Construct,Let) *)

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
  | Cut (i, a, c1, c2) -> fprintf fmt "Cut (@[%a, %a,@ @[<4>%a@],@ @[<4>%a@])@]" pra i prb a prc c1 prc c2
  | Let (x, i, c) -> fprintf fmt "Let (%a, %a,@ %a)" prb x pra i prc c
  | Rename (i1, i2, c) -> fprintf fmt "Rename (%a, %a,@ %a)" pra i1 pra i2 prc c
  | Axiom (i1, i2) -> fprintf fmt "Axiom (%a, %a)" pra i1 pra i2
  | Trivial i -> fprintf fmt "Trivial %a" pra i
  | Unfold (i, c) -> fprintf fmt "Unfold (%a,@ %a)" pra i prc c
  | Fold (i, c) -> fprintf fmt "Fold (%a,@ %a)" pra i prc c
  | Split (i, c1, c2) -> fprintf fmt "Split (@[%a,@ @[<4>%a@],@ @[<4>%a@])@]" pra i prc c1 prc c2
  | Destruct (i, j1, j2, c) ->
      fprintf fmt "Destruct (%a, %a, %a,@ %a)" pra i pra j1 pra j2 prc c
  | Construct (i1, i2, j, c) ->
      fprintf fmt "Construct (%a, %a, %a,@ %a)" pra i1 pra i2 pra j prc c
  | Swap (i, c) -> fprintf fmt "Swap (%a,@ %a)" pra i prc c
  | Dir (b, i, c) ->
      fprintf fmt "Dir (%b, %a,@ %a)" b pra i prc c
  | Weakening (i, c) -> fprintf fmt "Weakening@ (%a,@ %a)" pra i prc c
  | IntroQuant (i, y, c) -> fprintf fmt "IntroQuant (%a, %a,@ %a)" pra i pri y prc c
  | InstQuant (i, j, t, c) -> fprintf fmt "InstQuant (%a, %a, %a,@ %a)" pra i pra j prb t prc c
  | Rewrite (i, h, c) -> fprintf fmt "Rewrite (%a, %a,@ %a)" pra i pra h prc c

and prli = prle "; " pri
and prcertif fmt (v, c) = fprintf fmt  "%a,@ @[%a@]" prli v (prcab prpr Pretty.print_term) c
and prcore_certif fmt (v, c) = fprintf fmt  "%a,@ @[%a@]" prli v (prcab pri pcte) c

let eprcertif c = eprintf "%a@." prcertif c


let find_ident s h cta =
  match Mid.find_opt h cta.gamma_delta with
  | Some x -> x
  | None ->
      fprintf str_formatter "%s : Can't find ident %a in the task" s pri h;
      verif_failed (flush_str_formatter ())


(** Utility functions on certificates *)

(* Use propagate to define recursive functions on elements of type cert *)
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
  | Fold (i, c) -> Fold (fid i, f c)
  | Split (i, c1, c2) ->
      let f1 = f c1 in let f2 = f c2 in
      Split (fid i, f1, f2)
  | Destruct (i, j1, j2, c) -> Destruct (fid i, fid j1, fid j2, f c)
  | Construct (i1, i2, j, c) -> Construct (fid i1, fid i2, fid j, f c)
  | Swap (i, c) -> Swap (fid i, f c)
  | Dir (d, i, c) -> Dir (d, fid i, f c)
  | Weakening (i, c) -> Weakening (fid i, f c)
  | IntroQuant (i, y, c) -> IntroQuant (fid i, y, f c)
  | InstQuant (i, j, t, c) -> InstQuant (fid i, fid j, fte t, f c)
  | Rewrite (i, h, c) -> Rewrite (fid i, fid h, f c)

let rec fill map = function
  | Hole x -> Mid.find x map
  | c -> propagate_cert (fill map) (fun t -> t) (fun t -> t) c

let thunk (ids, c) () =
  let nids = new_idents (List.length ids) in
  let hole_nids = List.map (fun i -> Hole i) nids in
  let map = Mid.of_list (List.combine ids hole_nids) in
  nids, fill map c

let flatten_uniq l =
  let add (s, l) v = if Sid.mem v s
                     then s, l
                     else Sid.add v s, v::l in
  let add_list acc nl = List.fold_left add acc nl in
  let add_list_list acc nll = List.fold_left add_list acc nll in
  let _, fl = add_list_list (Sid.empty, []) l in
  List.rev fl

let (|>>>) (v1, c1) lcv2 =
  let lv2, lc2 = List.split lcv2 in
  assert (List.length v1 = List.length lv2);
  let lvc1 = List.combine v1 lc2 in
  let map = List.fold_left (fun map (v, c) -> Mid.add v c map) Mid.empty lvc1 in
  flatten_uniq lv2, fill map c1

let rec iterate n v = if n = 0 then [] else v :: iterate (n-1) v

let (|>>) (v1, c1) (v2, c2) =
  let n = List.length v1 in
  let lcv2 = iterate n (v2, c2) in
  (v1, c1) |>>> lcv2

let (||>) (v1, c1) f =
  let n = List.length v1 in
  let lcv2 = List.map f (iterate n ()) in
  (v1, c1) |>>> lcv2

(* Use propagate to define recursive functions on elements of type ecert *)
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
  | EFoldArr (g, a, b, i, c) -> EFoldArr (g, ft a, ft b, fid i, f c)
  | EDestruct (g, a, b, i, j1, j2, c) -> EDestruct (g, ft a, ft b, fid i, fid j1, fid j2, f c)
  | EConstruct (g, a, b, i1, i2, j, c) -> EConstruct (g, ft a, ft b, fid i1, fid i2, fid j, f c)
  | ESwap (g, a, i, c) -> ESwap (g, ft a, fid i, f c)
  | ESwapNeg (g, a, i, c) -> ESwapNeg (g, ft a, fid i, f c)
  | EWeakening (g, a, i, c) -> EWeakening (g, ft a, fid i, f c)
  | EIntroQuant (g, p, i, y, c) -> EIntroQuant (g, ft p, fid i, y, f c)
  | EInstQuant (g, p, i, j, t, c) -> EInstQuant (g, ft p, fid i, fid j, ft t, f c)
  | ERewrite (g, ty, a, b, ctxt, i, h, c) ->
      ERewrite (g, ty, ft a, ft b, ft ctxt, fid i, fid h, f c)


(* Separates hypotheses and goals *)
let split_hyp_goal cta =
  let open Mid in
  fold (fun h (ct, pos) (gamma, delta) ->
      if pos then gamma, add h (ct, pos) delta
      else add h (ct, pos) gamma, delta)
    cta (empty, empty)

(* Creates a new ctask with the same hypotheses but sets the goal with the second argument *)
let set_goal : ctask -> cterm -> ctask = fun cta ->
  let gamma, delta = split_hyp_goal cta.gamma_delta in
  let gpr, _ = Mid.choose gamma in
  fun ct -> { sigma = cta.sigma;
              gamma_delta = Mid.add gpr (ct, true) delta }


(** Compile chain.
    1. visible_cert
       The certificates given by certifying transformations.
       Many constructors and few parameters to ease making certifying
       a transformation.
    2. abstract_cert
       Same as before but with simpler types that can be used by our checkers.
       Also removes some easily derivable rules from other rules.
       An example of such easily derible rule is Dir.
    3. heavy_ecert
       The result of the elaboration and as such contains many additional
       information such as the current formula and whether the focus is on a
       goal or on a hypothesis.
    4. trimmed_ecert
       Same as before except that rules that are derivable with core rules when
       given additional information are replaced.
       Examples of such rules are Rename and Construct.
    5. kernel_ecert
       The certificates used by checkers.
       Few constructors and many parameters to ease formal verification of
       checkers.

*)

let dir_smart d prg c =
  let prh = create_prsymbol (id_fresh "Weaken") in
  let left, right = match d with false -> prg, prh | true -> prh, prg in
  Destruct (prg, left, right, Weakening (prh, c))


let rec abstract_cert = function
  | Dir (d, pr, c) -> abstract_cert (dir_smart d pr c)
  | c -> propagate_cert abstract_cert (fun pr -> pr.pr_name) abstract_term c

exception Elaboration_failed

module Hashid = Hashtbl.Make(struct type t = ident let equal = id_equal let hash = id_hash end)

let rewrite_ctask (cta : ctask) i a b ctxt =
  let ctxt = match ctxt with
    | CTquant (CTlambda, _, ctxt) -> ctxt
    | _ -> assert false in
  let ta = ct_open ctxt a in
  let tb = ct_open ctxt b in
  let rewrite_decl j (t, pos) =
    if id_equal j i && cterm_equal t ta
    then tb, pos
    else t, pos in
  lift_mid_cta (Mid.mapi rewrite_decl) cta

let rec replace_cterm tl tr t =
  if cterm_equal t tl
  then tr
  else cterm_map (replace_cterm tl tr) t

let elaborate (init_ct : ctask) c =
  let rec elab (cta : ctask) c =
  match c with
  | Nc -> eprintf "No certificates";
          raise Elaboration_failed
  | Hole i -> EHole i
  | Axiom (i1, i2) ->
      let a, posi2 = find_ident "Axiom" i2 cta in
      let i1, i2 = if posi2 then i1, i2 else i2, i1 in
      EAxiom (a, i1, i2)
  | Trivial i ->
      let _, pos = find_ident "Trivial" i cta in
      ETrivial (pos, i)
  | Rename (i1, i2, c) ->
      let a, pos = find_ident "Rename" i1 cta in
      let cta = remove i1 cta
                |> add i2 (a, pos) in
      let c = elab cta c in
      ERename (pos, a, i1, i2, c)
  | Cut (i, a, c1, c2) ->
      let cta1 = add i (a, true) cta in
      let cta2 = add i (a, false) cta in
      let c1 = elab cta1 c1 in
      let c2 = elab cta2 c2 in
      ECut (i, a, c1, c2)
  | Let (x, i, c) ->
      let y, _ = find_ident "Let" i cta in
      ELet (x, y, elab cta c)
  | Unfold (i, c) ->
      let t, pos = find_ident "Unfold" i cta in
      let iff, cta, t1, t2 = match t with
        | CTbinop (Tiff, t1, t2) ->
            let imp_pos = CTbinop (Timplies, t1, t2) in
            let imp_neg = CTbinop (Timplies, t2, t1) in
            let unfolded_iff = CTbinop (Tand, imp_pos, imp_neg), pos in
            true, add i unfolded_iff cta, t1, t2
        | CTbinop (Timplies, t1, t2) ->
            let unfolded_imp = CTbinop (Tor, CTnot t1, t2), pos in
            false, add i unfolded_imp cta, t1, t2
        | _ -> Format.eprintf "Nothing to unfold : @[%a@]@." pcte t;
               raise Elaboration_failed in
      let pack = pos, t1, t2, i, elab cta c in
      if iff
      then EUnfoldIff pack
      else EUnfoldArr pack
  | Fold (i, c) ->
      let t, pos = find_ident "Fold" i cta in
      let cta, t1, t2 = match t with
        | CTbinop (Tor, CTnot t1, t2) ->
            add i (CTbinop (Timplies, t1, t2), pos) cta, t1, t2
        | _ -> Format.eprintf "Nothing to fold : @[%a@]@." pcte t;
               raise Elaboration_failed in
      let c = elab cta c in
      EFoldArr (pos, t1, t2, i, c)
  | Split (i, c1, c2) ->
      let t, pos = find_ident "Split" i cta in
      let t1, t2 = match t, pos with
        | CTbinop (Tand, t1, t2), true | CTbinop (Tor, t1, t2), false -> t1, t2
        | _ -> eprintf "Not splittable";
               raise Elaboration_failed in
      let cta1 = add i (t1, pos) cta in
      let cta2 = add i (t2, pos) cta in
      let c1 = elab cta1 c1 in
      let c2 = elab cta2 c2 in
      ESplit (pos, t1, t2, i, c1, c2)
  | Destruct (i, j1, j2, c) ->
      let t, pos = find_ident "Destruct" i cta in
      let t1, t2 = match t, pos with
        | CTbinop (Tand, t1, t2), false | CTbinop (Tor, t1, t2), true -> t1, t2
        | _ -> eprintf "Nothing to destruct";
               raise Elaboration_failed in
      let cta = remove i cta
                |> add j1 (t1, pos)
                |> add j2 (t2, pos) in
      EDestruct (pos, t1, t2, i, j1, j2, elab cta c)
  | Construct (i1, i2, j, c) ->
      let t1, pos1 = find_ident "Construct1" i1 cta in
      let t2, pos2 = find_ident "Construct2" i2 cta in
      assert (pos1 = pos2);
      let t = if pos1
              then CTbinop (Tor, t1, t2)
              else CTbinop (Tand, t1, t2) in
      let cta = remove i1 cta
                |> remove i2
                |> add j (t, pos1) in
      EConstruct (pos1, t1, t2, i1, i2, j, elab cta c)
  | Swap (i, c) ->
      let t, pos = find_ident "Swap" i cta in
      let neg, underlying_t, neg_t = match t with
        | CTnot t -> true, t, t
        | _ -> false, t, CTnot t in
      let cta = add i (neg_t, not pos) cta in
      let pack = pos, underlying_t, i, elab cta c in
      if neg
      then ESwapNeg pack
      else ESwap pack
  | Dir _ -> verif_failed "Some Dir left during elaboration"
  | Weakening (i, c) ->
      let t, pos = find_ident "Weakening" i cta in
      let cta = remove i cta in
      EWeakening (pos, t, i, elab cta c)
  | IntroQuant (i, y, c) ->
      let t, pos = find_ident "IntroQuant" i cta in
      let t, ty = match t, pos with
        | CTquant (CTforall, ty, t), true | CTquant (CTexists, ty, t), false -> t, ty
        | _ -> eprintf "Nothing to introduce";
               raise Elaboration_failed in
      let cta = add i (ct_open t (CTfvar y), pos) cta
                |> add_var y ty in (* signature is not useful when elaborating for now... *)
      EIntroQuant (pos, CTquant (CTlambda, ty, t), i, y, elab cta c)
  | InstQuant (i, j, t_inst, c) ->
      let t, pos = find_ident "InstQuant" i cta in
      let t, ty = match t, pos with
        | CTquant (CTforall, ty, t), false | CTquant (CTexists, ty, t), true -> t, ty
        | _ -> eprintf "trying to instantiate a non-quantified hypothesis";
               raise Elaboration_failed in
      let cta = add j (ct_open t t_inst, pos) cta in
      EInstQuant (pos, CTquant (CTlambda, ty, t), i, j, t_inst, elab cta c)
  | Rewrite (i, h, c) ->
      let rew_hyp, _ = find_ident "Finding rewrite hypothesis" h cta in
      let a, b = match rew_hyp with
        | CTbinop (Tiff, a, b) -> a, b
        | CTapp (CTapp (f, a), b) when cterm_equal f eq -> a, b
        | _ -> eprintf "Rewrite hypothesis is badly-formed : %a" pcte rew_hyp;
               raise Elaboration_failed in
      let t, pos = find_ident "Finding to be rewritten goal" i cta in
      let id = id_register (id_fresh "ctxt_var") in
      let v = CTfvar id in
      let cty = infer_type cta.sigma a in
      let ctxt = CTquant (CTlambda, cty, ct_close id (replace_cterm a v t)) in
      let cta = rewrite_ctask cta i a b ctxt in
      ERewrite (pos, cty, a, b, ctxt, i, h, elab cta c)
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


let rec trim_certif c =
  match c with
  | ERename (g, a, i1, i2, c) ->
      let c = trim_certif c in
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
  | EFoldArr (g, a, b, i, c) ->
      let c = trim_certif c in
      let j = id_register (id_fresh "fold_arr_temp") in
      let pre = CTbinop (Tor, CTnot a, b) in
      let post = CTbinop (Timplies, a, b) in
      let c_open = EWeakening (g, pre, j, c) in
      let c_closed = EUnfoldArr (not g, a, b, i, eaxiom g pre i j) in
      let c1, c2 = if g then c_open, c_closed else c_closed, c_open in
      erename g pre i j (ECut (i, post, c1, c2))
  | _ -> propagate_ecert trim_certif (fun t -> t) (fun i -> i) c

let rec eliminate_let m c =
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

let make_core (init_ct : ctask) (_ : ctask list) (v, c : visible_cert) : heavy_ecert =
  (* Format.eprintf "%a@." prcertif c; *)
  v, abstract_cert c
     |> elaborate init_ct
     |> trim_certif
     |> eliminate_let Mid.empty
