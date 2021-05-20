open Why3
open Decl
open Term
open Ty
open Ident
open Format

open Cert_syntax
open Cert_abstract

(** We equip each transformation application with a certificate indicating
    why the list of resulting tasks implies the initial task *)

(* We will denote a ctask <{sigma; gamma_delta}> by <Σ | Γ ⊢ Δ>
   We sometimes omit the signature (when it's not confusing) and write <Γ ⊢ Δ> *)

type sc =
  | Nc
  | Hole of cterm ctask
  (* You should never use the Hole certificate *)
  | Assert of prsymbol * (term Mid.t -> term) * sc * sc
  | Let of term * prsymbol * sc
  (* Let (x, i, c) ⇓ t ≜  c[x → i(t)] ⇓ t *)
  (* Meaning : in c, x is mapped to the formula identified by i in task t *)
  | Axiom of prsymbol * prsymbol
  (* Axiom (i1, i2) ⇓ (Γ, i1 : t ⊢ Δ, i2 : t) stands *)
  (* Axiom (i1, i2) ⇓ (Γ, i2 : t ⊢ Δ, i1 : t) stands *)
  | Trivial of prsymbol
  (* Trivial i ⇓ (Γ, i : false ⊢ Δ) stands *)
  (* Trivial i ⇓ (Γ ⊢ Δ, i : true ) stands *)
  (* Trivial i ⇓ (Γ ⊢ Δ, i : t = t) stands *)
  | EqSym of prsymbol * sc
  (* EqSym (i, c) ⇓ (Γ ⊢ Δ, i : t₁ = t₂) ≜  c ⇓ (Γ ⊢ Δ, i : t₂ = t₁) *)
  (* EqSym (i, c) ⇓ (Γ, i : t₁ = t₂ ⊢ Δ) ≜  c ⇓ (Γ, i : t₂ = t₁ ⊢ Δ) *)
  | EqTrans of prsymbol * prsymbol * prsymbol * sc
  (* EqTrans (i₁, i₂, i₃, c) ⇓ (Γ, i₁ : t₁ = t₂, i₂ : t₂ = t₃ ⊢ Δ) ≜
     c ⇓ (Γ, i₁ : t₁ = t₂, i₂ : t₂ = t₃, i₃ : t₁ = t₃ ⊢ Δ) *)
  | Unfold of prsymbol * sc
  (* Unfold (i, c) ⇓ (Γ, i : t₁ ↔ t₂ ⊢ Δ) ≜
     c ⇓ (Γ, i : (t₁ → t₂) ∧ (t₂ → t₁) ⊢ Δ) *)
  (* Unfold (i, c) ⇓ (Γ ⊢ Δ, i : t₁ ↔ t₂) ≜
     c ⇓ (Γ ⊢ Δ, i : (t₁ → t₂) ∧ (t₂ → t₁)) *)
  (* Unfold (i, c) ⇓ (Γ, i : t₁ → t₂ ⊢ Δ) ≜  c ⇓ (Γ, i : ¬t₁ ∨ t₂ ⊢ Δ)*)
  (* Unfold (i, c) ⇓ (Γ ⊢ Δ, i : t₁ → t₂) ≜  c ⇓ (Γ ⊢ Δ, i : ¬t₁ ∨ t₂)*)
  | Fold of prsymbol * sc
  (* Fold (i, c) ⇓ (Γ, i : (t₁ → t₂) ∧ (t₂ → t₁) ⊢ Δ) ≜
     c ⇓ (Γ, i : t₁ ↔ t₂ ⊢ Δ) *)
  (* Fold (i, c) ⇓ (Γ ⊢ Δ, i : (t₁ → t₂) ∧ (t₂ → t₁)) ≜
     c ⇓ (Γ ⊢ Δ, i : t₁ ↔ t₂) *)
  (* Fold (i, c) ⇓ (Γ, i : ¬t₁ ∨ t₂ ⊢ Δ) ≜  c ⇓ (Γ, i : t₁ → t₂ ⊢ Δ) *)
  (* Fold (i, c) ⇓ (Γ ⊢ Δ, i : ¬t₁ ∨ t₂) ≜  c ⇓ (Γ ⊢ Δ, i : t₁ → t₂) *)
  | Split of prsymbol * sc * sc
  (* Split (i, c₁, c₂) ⇓ (Γ, i : t₁ ∨ t₂ ⊢ Δ) ≜
     c₁ ⇓ (Γ, i : t₁ ⊢ Δ)
     and c₂ ⇓ (Γ, i : t₂ ⊢ Δ) *)
  (* Split (i, c₁, c₂) ⇓ (Γ ⊢ Δ, i : t₁ ∧ t₂) ≜
     c₁ ⇓ (Γ ⊢ Δ, i : t₁)
     and c₂ ⇓ (Γ ⊢ Δ, i : t₂) *)
  | Destruct of prsymbol * prsymbol * prsymbol * sc
  (* Destruct (i, i₁, i₂, c) ⇓ (Γ, i : t₁ ∧ t₂ ⊢ Δ) ≜
     c ⇓ (Γ, i₁ : t₁, i₂ : t₂ ⊢ Δ) *)
  (* Destruct (i, i₁, i₂, c) ⇓ (Γ ⊢ Δ, i : t₁ ∨ t₂) ≜
     c ⇓ (Γ ⊢ Δ, i₁ : t₁, i₂ : t₂) *)
  | Construct of prsymbol * prsymbol * prsymbol * sc
  (* Construct (i₁, i₂, i, c) ⇓ (Γ, i₁ : t₁, i₂ : t₂ ⊢ Δ) ≜
     c ⇓ (Γ, i : t₁ ∧ t₂ ⊢ Δ) *)
  (* Construct (i₁, i₂, i, c) ⇓ (Γ ⊢ Δ, i₁ : t₁, i₂ : t₂) ≜
     c ⇓ (Γ ⊢ Δ, i : t₁ ∧ t₂) *)
  | Swap of prsymbol * sc
  (* Swap (i, c) ⇓ (Γ, i : ¬t ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ, i : t) *)
  (* Swap (i, c) ⇓ (Γ, i : t ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ, i : ¬t) *)
  (* Swap (i, c) ⇓ (Γ ⊢ Δ, i : t) ≜  c ⇓ (Γ, i : ¬t ⊢ Δ) *)
  (* Swap (i, c) ⇓ (Γ ⊢ Δ, i : ¬t) ≜  c ⇓ (Γ, i : t ⊢ Δ) *)
  | Clear of prsymbol * sc
  (* Clear (i, c) ⇓ (Γ ⊢ Δ, i : t) ≜  c ⇓ (Γ ⊢ Δ) *)
  (* Clear (i, c) ⇓ (Γ, i : t ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ) *)
  | Forget of lsymbol * sc
  (* Forget (i, c) ⇓ (Σ, i | Γ ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ) *)
  | Duplicate of prsymbol * prsymbol * sc
  (* Duplicate (i₁, i₂, c) ⇓ (Γ ⊢ Δ, i₁ : t) ≜  c ⇓ (Γ ⊢ Δ, i₁ : t, i₂ : t) *)
  (* Duplicate (i₁, i₂, c) ⇓ (Γ, i₁ : t ⊢ Δ) ≜  c ⇓ (Γ, i₁ : t, i₂ : t ⊢ Δ) *)
  | IntroQuant of prsymbol * lsymbol * sc
  (* IntroQuant (i, y, c) ⇓ (Σ | Γ, i : ∃ x : τ. p ⊢ Δ) ≜
     c ⇓ (Σ, y : τ | Γ, i : p[x ↦ y] ⊢ Δ)
     and y ∉  Σ *)
  (* IntroQuant (i, y, c) ⇓ (Σ | Γ ⊢ Δ, i : ∀ x : τ. p) ≜
     c ⇓ (Σ, y : τ | Γ ⊢ Δ, i : p[x ↦ y])
     and y ∉  Σ *)
  | InstQuant of prsymbol * prsymbol * term * sc
  (* InstQuant (i₁, i₂, t, c) ⇓ (Σ | Γ, i₁ : ∀ x : τ. p ⊢ Δ) ≜
     c ⇓ (Σ | Γ, i₁ : ∀ x : τ. p x, i₂ : p[x ↦ t] ⊢ Δ)
     and Σ ⊩ t : τ *)
  (* InstQuant (i₁, i₂, t, c) ⇓ (Σ | Γ ⊢ Δ, i₁ : ∃ x : τ. p) ≜
     c ⇓ (Σ | Γ ⊢ Δ, i₁ : ∃ x : τ. p x, i₂ : p[x ↦ t])
     and Σ ⊩ t : τ *)
  | Rewrite of prsymbol * prsymbol * sc
  (* Rewrite (i₁, i₂, c) ⇓ (Γ, i₁ : t₁ = t₂ ⊢ Δ, i₂ : ctxt[t₁]) ≜
     c ⇓ (Γ, i₁ : t₁ = t₂ ⊢ Δ, i₂ : ctxt[t₂]) *)
  (* Rewrite (i₁, i₂, c) ⇓ (Γ, H : t₁ = t₂, i₁ : ctxt[t₁] ⊢ Δ) ≜
     c ⇓ (Γ, H : t₁ = t₂, i₂ : ctxt[t₂] ⊢ Δ) *)
  | Induction of prsymbol * prsymbol * prsymbol * prsymbol * term * (term Mid.t -> term)
                 * sc * sc
(* Induction (G, Hi₁, Hi₂, Hr, x, a, c₁, c₂) ⇓ (Γ ⊢ Δ, G : ctxt[x]) ≜
   c₁ ⇓ (Γ, Hi₁ : i ≤ a ⊢ Δ, G : ctxt[x])
   and c₂ ⇓ (Γ, Hi₂ : a < i, Hr: ∀ n : int. n < i → ctxt[n] ⊢ ctxt[x])
   and i does not appear in Γ, Δ or C
   and x and a are of type int
 *)
(* In the induction and rewrite rules ctxt is a context and the notation ctxt[t]
   stands for this context where the holes have been replaced with t *)

type scert = int * (sc list -> sc)

let fail_arg () = verif_failed "Argument arity mismatch when composing certificates"

let fill_tasks (n, f) res_ct =
  if List.length res_ct = n
  then f (List.map (fun u -> Hole u) res_ct)
  else verif_failed "Wrong number of holes in certificate"

type 'a args =
  | Z : sc args
  | Succ : 'a args -> (sc -> 'a) args

let rec lambda : type a. a args -> a -> sc list -> sc = fun args f ->
  match args with
  | Z ->
      begin function
        | [] -> f
        | _  -> verif_failed "Too many arguments in certificate application" end
  | Succ args ->
      function
      | [] -> verif_failed "Missing arguments in certificate application"
      | h::l -> lambda args (f h) l

let rec arity : type a. a args -> int = fun args ->
  match args with
  | Z -> 0
  | Succ args -> arity args + 1

let newcert : type a. a args -> a -> scert = fun args f ->
  arity args, lambda args f

let return c = newcert Z c
let newcert1 f = newcert (Succ Z) f
let newcert2 f = newcert (Succ (Succ Z)) f
let newcertn n f = n, f

let apply ((_, f) : scert) : sc = f []

let lambda1 f = newcert1 (fun t -> apply (f t))
let lambda2 f = newcert2 (fun t1 t2 -> apply (f t1 t2))
let lambdan n f = newcertn n (fun l -> apply (f l))

let rec cut n = function
  | h::t when n > 0 ->
      let l1, l2 = cut (n-1) t in
      h::l1, l2
  | l -> [], l

let rec dispatch lu lc = match lc with
  | (n2, f2)::lc ->
      let lu2, lu = cut n2 lu in
      f2 lu2 :: dispatch lu lc
  | [] -> []

let (+++) (n1, f1) lc2 : scert =
  assert (List.length lc2 = n1);
  let n = List.fold_left (fun acc (n, _) -> acc + n) 0 lc2 in
  n, fun lu -> f1 (dispatch lu lc2)

let (++) (n1, f1) c2 : scert =
  let lc2 = Lists.init n1 (fun _ -> c2) in
  (n1, f1) +++ lc2

let nc : scert = return Nc
(* "no certificate", makes verification fail: use it as a placeholder *)
let idc : scert = newcert1 (fun t -> t)
(* For the identity transformation *)
let assertion p t = newcert2 (fun a1 a2 -> Assert (p, t, a1, a2))
(* Produces two new tasks: one with p : t added to the goals and
   one with p : t added to the hypotheses *)
let axiom p1 p2 = return (Axiom (p1, p2))
(* Closes the task when p1 and p2 contain the same formula and
   one is in the hypotheses while the other is in the goals *)
let trivial p = return (Trivial p)
(* Closes the task when p either contains ⊥ in the hypotheses,
   ⊤ in the goals or a formula of the form t = t in the goals *)
let eqsym p = newcert1 (fun a -> EqSym (p, a))
(* From a task with a premise of the form p : t₁ = t₂, produces the
   same task with premise p modified into p : t₂ = t₁ *)
let eqtrans h1 h2 h3 = newcert1 (fun a -> EqTrans (h1, h2, h3, a))
(* From a task with two hypotheses of the form h₁ : t₁ = t₂ and h₂ : t₂ = t₃,
   produces the same task with added hypothesis h₃ : t₁ = t₃*)
let unfold p = newcert1 (fun a -> Unfold (p, a))
(* From a task with a premise of the form p : t₁ → t₂ (resp. p : t₁ ↔ t₂),
   produces the same task with premise p modified into p : ¬ t₁ ∨ t₂
   (resp. p : (t₁ → t₂) ∧ (t₂ → t₁)) *)
let fold p = newcert1 (fun a -> Fold (p, a))
(* From a task with a premise of the form p : ¬ t₁ ∨ t₂
   (resp. p : (t₁ → t₂) ∧ (t₂ → t₁)), produces the same task with premise p
   modified into p : t₁ → t₂ (resp. p : t₁ ↔ t₂) *)
let split p = newcert2 (fun a1 a2 -> Split (p, a1, a2))
(* From a task with an hypothesis of the form p : t₁ ∨ t₂ (resp. a goal of the
   form p : t₁ ∧ t₂), produces two new tasks: one with hypothesis (resp. goal) p
   is replaced with p : t₁ and one with hypothesis (resp. goal) p is replaced with
   p : t₂ *)
let destruct p p1 p2 = newcert1 (fun a -> Destruct (p, p1, p2, a))
(* From a task with an hypothesis of the form p : t₁ ∧ t₂ (resp. a goal of
   the form p : t₁ ∨ t₂), produces the same task where hypothesis (resp. goal) p
   is replaced by two hypotheses (resp. goals) p₁ : t₁ and p₂ : t₂ *)
let construct p1 p2 p = newcert1 (fun a -> Construct (p1, p2, p, a))
(* From a task with hypotheses (resp. goals) of the form p₁ : t₁ and p₂ : t₂,
   produces the same task where hypotheses (resp. goals) p₁ and p₂ are replaced
   with hypothesis p : t₁ ∧ t₂ (resp. goal p : t₁ ∨ t₂) *)
let swap p = newcert1 (fun a -> Swap (p, a))
(* Puts an hypothesis (resp. a goal) into the goals (resp. the hypotheses),
   by negating it, removing double negation *)
let clear p = newcert1 (fun a -> Clear (p, a))
(* Removes a premise p from the task *)
let forget ls = newcert1 (fun a -> Forget (ls, a))
(* Removes an unused abstract type ls from the task *)
let duplicate p1 p2 =
  assert (not (pr_equal p1 p2));
  newcert1 (fun a -> Duplicate (p1, p2, a))
(* Duplicates a premise p₁ into p₂ *)
let introquant p y = newcert1 (fun a -> IntroQuant (p, y, a))
(* From a fresh variable y and a task with hypothesis p : ∃ x : τ. q
   (resp. goal p : ∀ x. q), produces a new task with the variable y of
   type \τ and hypothesis (resp. goal) p modified into p : q[x ↦ y] *)
let instquant p1 p2 t = newcert1 (fun a -> InstQuant (p1, p2, t, a))
(* From a term t of type τ and a task with hypothesis p₁ : ∀ x : τ. q
   (resp. goal p₁ : ∃ x. q), produces a new task with the variable y of
   type τ and the added hypothesis (resp. goal) p₂ : q[x ↦ t] *)
let rewrite h p = newcert1 (fun a -> Rewrite (h, p, a))
(* From a task with hypothesis h : t₁ = t₂ and premise p : t[t₁],
   produces the tasks with p modified into p : t[t₂] *)
let induction g hi1 hi2 hr x a =
  newcert2 (fun a1 a2 -> Induction (g, hi1, hi2, hr, x, a, a1, a2))
(* From an integer a and a task with a goal g : t[x] with x being an integer,
   produces two new tasks: one with the added hypothesis hi1 : i ≤ a and the
   other with the added hypotheses hi2 : a < i and hr : ∀ n. n < i → t[n] *)

let llet pr (cont : ident -> scert) : scert =
  let ls = create_psymbol (id_fresh "Let_var") [] in
  let t = t_app ls [] None in
  newcert1 (fun u -> Let (t, pr, u)) ++ cont ls.ls_name
(* From a task with premise pr : t, produces the same tasks as cont i,
   where i is mapped to t *)

let create_eqrefl h (t : term) =
  assertion h (fun _ -> t_app_infer ps_equ [t; t]) +++ [trivial h; idc]
(* Produces a task with the added hypothesis h : t = t *)

let rename p1 p2 =
  duplicate p1 p2 ++ clear p1
(* Renames a premise p₁ into p₂ *)

let dir d p =
  let q = create_prsymbol (id_fresh "dir") in
  let left, right = if d then q, p else p, q in
  destruct p left right ++ clear q
(* Chose a direction for hypothesis p : t₁ ∨ t₂ or goal p : t₁ ∧ t₂ *)

let iffsym_hyp h =
  let h1 = pr_clone h in
  let h2 = pr_clone h in
  unfold h ++
    destruct h h1 h2 ++
      construct h2 h1 h ++
        fold h
(* From a task with an hypothesis of the form h : t₁ ↔ t₂, produces the
   same task with premise h modified into h : t₂ ↔ t₁ *)

type ctrans = scert ctransformation


(* Replaying a certif cert against a ctask cta will be denoted <cert ⇓ cta>.
   For more details, take a look at the OCaml implementation
   <Cert_verif_caml.ccheck>. *)

(* ('v, 'h, 't, 'ty) kc is the type of kernel certificates, where:
   • 'v is used for variables
   • 'h is used for premise names
   • 't is used for terms
   • 'ty is used for types *)
type ('v, 'h, 't, 'ty) kc =
  | KHole of cterm ctask
  (* KHole cta ⇓ cta stands *)
  | KClear of bool * 't * 'h * ('v, 'h, 't, 'ty) kc
  (* KClear (true, t, i, c) ⇓ (Γ ⊢ Δ, i : t) ≜ c ⇓ (Γ ⊢ Δ) *)
  (* KClear (false, t, i, c) ⇓ (Γ, i : t ⊢ Δ) ≜ c ⇓ (Γ ⊢ Δ) *)
  | KDuplicate of bool * 't * 'h * 'h * ('v, 'h, 't, 'ty) kc
  (* not kernel *)
  | KForget of 'v * ('v, 'h, 't, 'ty) kc
  (* KForget (i, c) ⇓ (Σ, i : τ | Γ ⊢ Δ) ≜ c ⇓ (Γ ⊢ Δ) *)
  | KAssert of 'h * 't * ('v, 'h, 't, 'ty) kc * ('v, 'h, 't, 'ty) kc
  (* KAssert (i, t, c₁, c₂) ⇓ (Γ ⊢ Δ) ≜
     c₁ ⇓ (Γ ⊢ Δ, i : t) and
     c₂ ⇓ (Γ, i : t ⊢ Δ) *)
  | KAxiom of 't * 'h * 'h
  (* KAxiom (t, i1, i2) ⇓ (Γ, i1 : t ⊢ Δ, i2 : t) stands *)
  | KTrivial of bool * 'h
  (* KTrivial (false, i) ⇓ (Γ, i : ⊥ ⊢ Δ) stands *)
  (* KTrivial (true, i) ⇓ (Γ ⊢ Δ, i : ⊤) stands *)
  | KSwap of (bool * 't * 'h * ('v, 'h, 't, 'ty) kc)
  (* KSwap (false, t, i, c) ⇓ (Γ, i : t ⊢ Δ) ≜ c ⇓ (Γ ⊢ Δ, i : ¬t) *)
  (* KSwap (true, t, i, c) ⇓ (Γ ⊢ Δ, i : t) ≜ c ⇓ (Γ, i : ¬t ⊢ Δ) *)
  | KSwapNeg of (bool * 't * 'h * ('v, 'h, 't, 'ty) kc)
  (* KSwapNeg (false, t, i, c) ⇓ (Γ, i : ¬t ⊢ Δ) ≜ c ⇓ (Γ ⊢ Δ, i : t)  *)
  (* KSwapNeg (true, t, i, c) ⇓ (Γ ⊢ Δ, i : ¬t) ≜ c ⇓ (Γ, i : t ⊢ Δ)  *)
  | KUnfoldIff of (bool * 't * 't * 'h * ('v, 'h, 't, 'ty) kc)
  (* KUnfoldIff (false, t₁, t₂, i, c) ⇓ (Γ, i : t₁ ↔ t₂ ⊢ Δ) ≜
     c ⇓ (Γ, i : (t₁ → t₂) ∧ (t₂ → t₁) ⊢ Δ) *)
  (* KUnfoldIff (true, t₁, t₂, i, c) ⇓ (Γ ⊢ Δ, i : t₁ ↔ t₂) ≜
     c ⇓ (Γ ⊢ Δ, i : (t₁ → t₂) ∧ (t₂ → t₁)) *)
  | KUnfoldArr of (bool * 't * 't * 'h * ('v, 'h, 't, 'ty) kc)
  (* KUnfoldArr (false, t₁, t₂, i, c) ⇓ (Γ, i : t₁ → t₂ ⊢ Δ) ≜
     c ⇓ (Γ, i : ¬t₁ ∨ t₂ ⊢ Δ)*)
  (* KUnfoldArr (true, t₁, t₂, i, c) ⇓ (Γ ⊢ Δ, i : t₁ → t₂) ≜
     c ⇓ (Γ ⊢ Δ, i : ¬t₁ ∨ t₂)*)
  | KFoldIff of (bool * 't * 't * 'h * ('v, 'h, 't, 'ty) kc)
  (* not kernel *)
  | KFoldArr of (bool * 't * 't * 'h * ('v, 'h, 't, 'ty) kc)
  (* not kernel *)
  | KSplit of bool * 't * 't * 'h * ('v, 'h, 't, 'ty) kc * ('v, 'h, 't, 'ty) kc
  (* KSplit (false, t₁, t₂, i, c₁, c₂) ⇓ (Γ, i : t₁ ∨ t₂ ⊢ Δ) ≜
     c₁ ⇓ (Γ, i : t₁ ⊢ Δ) and
     c₂ ⇓ (Γ, i : t₂ ⊢ Δ) *)
  (* KSplit (true, t₁, t₂, i, c₁, c₂) ⇓ (Γ ⊢ Δ, i : t₁ ∧ t₂) ≜
     c₁ ⇓ (Γ ⊢ Δ, i : t₁) and
     c₂ ⇓ (Γ ⊢ Δ, i : t₂) *)
  | KDestruct of bool * 't * 't * 'h * 'h * 'h * ('v, 'h, 't, 'ty) kc
  (* KDestruct (false, t₁, t₂, i, i₁, i₂, c) ⇓ (Γ, i : t₁ ∧ t₂ ⊢ Δ) ≜
     c ⇓ (Γ, i₁ : t₁, i₂ : t₂ ⊢ Δ) *)
  (* KDestruct (true, t₁, t₂, i, i₁, i₂, c) ⇓ (Γ ⊢ Δ, i : t₁ ∨ t₂) ≜
     c ⇓ (Γ ⊢ Δ, i₁ : t₁, i₂ : t₂) *)
  | KConstruct of bool * 't * 't * 'h * 'h * 'h * ('v, 'h, 't, 'ty) kc
  (* not kernel *)
  | KIntroQuant of bool * 'ty * 't * 'h * 'v * ('v, 'h, 't, 'ty) kc
  (* KIntroQuant (false, τ, p, i, y, c) ⇓ (Σ | Γ, i : ∃ x : τ. p ⊢ Δ) ≜
     c ⇓ (Σ, y : τ | Γ, i : p[x ↦ y] ⊢ Δ)
     and y ∉ Σ *)
  (* KIntroQuant (true, τ, p, i, y, c) ⇓ (Σ | Γ ⊢ Δ, i : ∀ x : τ. p) ≜
     c ⇓ (Σ, y : τ | Γ ⊢ Δ, i : p[x ↦ y])
     and y ∉ Σ *)
  | KInstQuant of bool * 'ty * 't * 'h * 'h * 't * ('v, 'h, 't, 'ty) kc
  (* KInstQuant (false, τ, p, i₁, i₂, t, c) ⇓ (Σ | Γ, i₁ : ∀ x : τ. p ⊢ Δ) ≜
     c ⇓ (Σ | Γ, i₁ : ∀ x : τ. p, i₂ : p[x ↦ t] ⊢ Δ)
     and Σ ⊩ t : τ *)
  (* KInstQuant (true, τ, p, i₁, i₂, t, c) ⇓ (Σ | Γ ⊢ Δ, i₁ : ∃ x : τ. p) ≜
     c ⇓ (Σ | Γ ⊢ Δ, i₁ : ∃ x : τ. p x, i₂ : p[x ↦ t])
     and Σ ⊩ t : τ *)
  | KEqRefl of 'ty * 't * 'h
  (* KEqRefl (τ, t, i) ⇓ (Γ ⊢ Δ, i : t = t) stands if t is of type τ *)
  | KEqSym of bool * 'ty * 't * 't * 'h * ('v, 'h, 't, 'ty) kc
  (* not kernel *)
  | KEqTrans of 'ty * 't * 't * 't * 'h * 'h * 'h * ('v, 'h, 't, 'ty) kc
  (* not kernel *)
  | KRewrite of bool * 't option * 'ty * 't * 't * 't * 'h * 'h
                * ('v, 'h, 't, 'ty) kc
  (* KRewrite (true, None, τ, t₁, t₂, ctxt, i₁, i₂, c) ⇓
     (Γ, i₁ : t₁ = t₂ ⊢ Δ, i₂ : ctxt[t₁]) ≜
     c ⇓ (Γ, i₁ : t₁ = t₂ ⊢ Δ, i₂ : ctxt[t₂]) *)
  (* KRewrite (false, None, τ, t₁, t₂, ctxt, i₁, i₂, c) ⇓
     (Γ, i₁ : t₁ = t₂, i₂ : ctxt[t₁] ⊢ Δ) ≜
     c ⇓ (Γ, i₁ : t₁ = t₂, i₂ : ctxt[t₂] ⊢ Δ) *)
  (* KRewrite (true, Some _, τ, t₁, t₂, ctxt, i₁, i₂, c) ⇓
     (Γ, i₁ : t₁ ↔ t₂ ⊢ Δ, i₂ : ctxt[t₁]) ≜
     c ⇓ (Γ, i₁ : t₁ ↔ t₂ ⊢ Δ, i₂ : ctxt[t₂]) *)
  (* KRewrite (false, Some _, τ, t₁, t₂, ctxt, i₁, i₂, c) ⇓
     (Γ, i₁ : t₁ ↔ t₂, i₂ : ctxt[t₁] ⊢ Δ) ≜
     c ⇓ (Γ, i₁ : t₁ ↔ t₂, i₂ : ctxt[t₂] ⊢ Δ) *)
  | KInduction of 'h * 'h * 'h * 'h * 't * 't * 't
                  * ('v, 'h, 't, 'ty) kc * ('v, 'h, 't, 'ty) kc
(* KInduction (G, Hi₁, Hi₂, Hr, x, a, ctxt, c₁, c₂) ⇓ (Γ ⊢ Δ, G : ctxt[x]) ≜
   c₁ ⇓ (Γ, Hi₁ : i ≤ a ⊢ Δ, G : ctxt[x]) and
   c₂ ⇓ (Γ, Hi₂ : a < i, Hr: ∀ n : int. n < i → ctxt[n] ⊢ ctxt[x])
   and i does not appear in Γ, Δ or C
   and x and a are of type int *)
(* In the induction and rewrite rules ctxt is a context and the notation ctxt[t]
   stands for this context where the holes have been replaced with t *)

type wkc = (lsymbol, prsymbol, term, ty option) kc
type kcert = (ident, ident, cterm, ctype) kc

let rec print_certif filename cert =
  let oc = open_out filename in
  let fmt = formatter_of_out_channel oc in
  fprintf fmt "%a@." prcertif cert;
  close_out oc

and prc fmt c =
  let prt = Pretty.print_term in
  match c with
  | Nc -> fprintf fmt "No_certif"
  | Hole ct -> fprintf fmt "Hole %a" prid ct.uid
  | Assert (i, _, c1, c2) ->
      fprintf fmt "Assert (@[%a, <fun>,@ @[<4>%a@],@ @[<4>%a@])@]"
        prpr i prc c1 prc c2
  | Let (x, i, c) -> fprintf fmt "Let (%a, %a,@ %a)" prt x prpr i prc c
  | Axiom (i1, i2) -> fprintf fmt "Axiom (%a, %a)" prpr i1 prpr i2
  | Trivial i -> fprintf fmt "Trivial %a" prpr i
  | EqSym (i, c) -> fprintf fmt "EqSym (%a,@ %a)" prpr i prc c
  | EqTrans (i1, i2, i3, c) -> fprintf fmt "EqTrans (%a, %a, %a, @ %a)"
                                 prpr i1 prpr i2 prpr i3 prc c
  | Unfold (i, c) -> fprintf fmt "Unfold (%a,@ %a)" prpr i prc c
  | Fold (i, c) -> fprintf fmt "Fold (%a,@ %a)" prpr i prc c
  | Split (i, c1, c2) -> fprintf fmt "Split (@[%a,@ @[<4>%a@],@ @[<4>%a@])@]"
                           prpr i prc c1 prc c2
  | Destruct (i, j1, j2, c) ->
      fprintf fmt "Destruct (%a, %a, %a,@ %a)" prpr i prpr j1 prpr j2 prc c
  | Construct (i1, i2, j, c) ->
      fprintf fmt "Construct (%a, %a, %a,@ %a)" prpr i1 prpr i2 prpr j prc c
  | Swap (i, c) -> fprintf fmt "Swap (%a,@ %a)" prpr i prc c
  | Clear (i, c) -> fprintf fmt "Clear@ (%a,@ %a)" prpr i prc c
  | Forget (v, c) -> fprintf fmt "Forget@ (%a,@ %a)" prls v prc c
  | Duplicate (i1, i2, c) -> fprintf fmt "Duplicate@ (%a, %a, @ %a)"
                               prpr i1 prpr i2 prc c
  | IntroQuant (i, y, c) -> fprintf fmt "IntroQuant (%a, %a,@ %a)"
                              prpr i prls y prc c
  | InstQuant (i, j, t, c) -> fprintf fmt "InstQuant (%a, %a, %a,@ %a)"
                                prpr i prpr j prt t prc c
  | Rewrite (i, h, c) -> fprintf fmt "Rewrite (%a, %a,@ %a)" prpr i prpr h prc c
  | Induction (i1, i2, i3, i4, x, _, c1, c2) ->
      fprintf fmt "Induction (%a, %a, %a, %a, %a, <fun>,@ %a,@ %a)"
        prpr i1 prpr i2 prpr i3 prpr i4 prt x prc c1 prc c2

and prlid = pp_print_list ~pp_sep:(fun fmt () -> pp_print_string fmt "; ") prid
and prcertif fmt (n, c) =
  let cts = Lists.init n dummy_ctask in
  let lid = List.map (fun ct -> ct.uid) cts in
  let c = fill_tasks (n, c) cts in
  fprintf fmt "@[<v>[%a],@ @[%a@]@]"
    prlid lid prc c;
  List.iter (forget_id ip) lid

let eprcertif c = eprintf "%a@." prcertif c


(** Utility functions on certificates *)

(* To define recursive functions on elements of type sc *)
let map_sc fc = function
  | (Hole _ | Nc) as c -> c
  | Axiom (h, g) -> Axiom (h, g)
  | Trivial i -> Trivial (i)
  | EqSym (i, c) -> EqSym (i, fc c)
  | EqTrans (i1, i2, i3, c) -> EqTrans (i1, i2, i3, fc c)
  | Assert (i, a, c1, c2) ->
      let f1 = fc c1 in
      let f2 = fc c2 in
      Assert (i, a, f1, f2)
  | Let (x, i, c) -> Let (x, i, fc c)
  | Unfold (i, c) -> Unfold (i, fc c)
  | Fold (i, c) -> Fold (i, fc c)
  | Split (i, c1, c2) ->
      let f1 = fc c1 in let f2 = fc c2 in
                        Split (i, f1, f2)
  | Destruct (i, j1, j2, c) -> Destruct (i, j1, j2, fc c)
  | Construct (i1, i2, j, c) -> Construct (i1, i2, j, fc c)
  | Swap (i, c) -> Swap (i, fc c)
  | Clear (i, c) -> Clear (i, fc c)
  | Forget (v, c) -> Forget (v, fc c)
  | Duplicate (i1, i2, c) -> Duplicate (i1, i2, fc c)
  | IntroQuant (i, y, c) -> IntroQuant (i, y, fc c)
  | InstQuant (i, j, t, c) -> InstQuant (i, j, t, fc c)
  | Rewrite (i, h, c) -> Rewrite (i, h, fc c)
  | Induction (i1, i2, i3, i4, n, t, c1, c2) ->
      Induction (i1, i2, i3, i4, n, t, fc c1, fc c2)

(* To define recursive functions on elements of type kc *)
let map_kc fc fv fh ft fty = function
  | KHole _ as c -> c
  | KAssert (i, a, c1, c2) ->
      let f1 = fc c1 in
      let f2 = fc c2 in
      KAssert (fh i, ft a, f1, f2)
  | KAxiom (a, i1, i2) -> KAxiom (ft a, fh i1, fh i2)
  | KTrivial (pos, i) -> KTrivial (pos, fh i)
  | KEqRefl (ty, t, i) -> KEqRefl (fty ty, ft t, fh i)
  | KEqSym (pos, ty, t1, t2, i, c) ->
      KEqSym (pos, fty ty, ft t1, ft t2, fh i, fc c)
  | KEqTrans (ty, t1, t2, t3, i1, i2, i3, c) ->
      KEqTrans (fty ty, ft t1, ft t2, ft t3, fh i1, fh i2, fh i3, fc c)
  | KSplit (pos, a, b, i, c1, c2) ->
      let f1 = fc c1 in
      let f2 = fc c2 in
      KSplit (pos, ft a, ft b, fh i, f1, f2)
  | KUnfoldIff (pos, a, b, i, c) -> KUnfoldIff (pos, ft a, ft b, fh i, fc c)
  | KUnfoldArr (pos, a, b, i, c) -> KUnfoldArr (pos, ft a, ft b, fh i, fc c)
  | KFoldIff (pos, a, b, i, c) -> KFoldIff (pos, ft a, ft b, fh i, fc c)
  | KFoldArr (pos, a, b, i, c) -> KFoldArr (pos, ft a, ft b, fh i, fc c)
  | KDestruct (pos, a, b, i, j1, j2, c) ->
      KDestruct (pos, ft a, ft b, fh i, fh j1, fh j2, fc c)
  | KConstruct (pos, a, b, i1, i2, j, c) ->
      KConstruct (pos, ft a, ft b, fh i1, fh i2, fh j, fc c)
  | KSwap (pos, a, i, c) -> KSwap (pos, ft a, fh i, fc c)
  | KSwapNeg (pos, a, i, c) -> KSwapNeg (pos, ft a, fh i, fc c)
  | KClear (pos, a, i, c) -> KClear (pos, ft a, fh i, fc c)
  | KForget (i, c) -> KForget (fv i, fc c)
  | KDuplicate (pos, a, i1, i2, c) -> KDuplicate (pos, ft a, fh i1, fh i2, fc c)
  | KIntroQuant (pos, ty, p, i, y, c) ->
      KIntroQuant (pos, fty ty, ft p, fh i, fv y, fc c)
  | KInstQuant (pos, ty, p, i, j, t, c) ->
      KInstQuant (pos, fty ty, ft p, fh i, fh j, ft t, fc c)
  | KRewrite (pos, topt, ty, a, b, ctxt, i, h, c) ->
      KRewrite (pos, Opt.map ft topt, fty ty, ft a, ft b, ft ctxt, fh i, fh h, fc c)
  | KInduction (i1, i2, i3, i4, n, t, ctxt, c1, c2) ->
      KInduction (fh i1, fh i2, fh i3, fh i4, ft n, ft t, ft ctxt, fc c1, fc c2)

(* <abstract_terms_types> also simplifies all symbols into ident, and
   builds the context to rewrite formulas (this is a function that cannot be
   defined as a Why3.term) *)
let rec abstract_terms_types (l : wkc) : kcert = match l with
  | KRewrite (pos, Some {t_node = Tapp (ls, [])}, None, a, b, ctxt, i, h, c) ->
      let ntls = CTfvar (ls.ls_name, []) in
      let cctxt = abstract_term ctxt in
      let nctxt = CTquant (CTlambda, CTprop, ct_close ls.ls_name cctxt) in
      let na = abstract_term a in
      let nb = abstract_term b in
      let nc = abstract_terms_types c in
      KRewrite (pos, Some ntls, CTprop, na, nb, nctxt, i.pr_name, h.pr_name, nc)
  | c -> map_kc abstract_terms_types
           (fun ls -> ls.ls_name) (fun pr -> pr.pr_name)
           abstract_term abstract_otype c

(** Compile chain.
    1. surface certificates : scert
       The certificates returned by certifying transformations.
       Many constructors and few parameters to ease making certifying
       a transformation.
    2. applied certificates : sc
       Result of the function <elab_apply>, this is not a function anymore.
    3. elaborated certificates : wkc
       Result of the main elaboration function <elaborate> and as such contains
       many additional information such as the current formula and whether the focus
       is on a goal or on an hypothesis. Knowing those additional informations,
       Let-variables can be substituted
    4. abstracted kernel certificates : kcert
       Result of applying the <abstract_terms_types>. Same as before but with
       simpler symbols, terms and types that can be used by our checkers.
    5. trimmed certificates : kcert
       Result of the function <trim>. It trims the certificate of rules that are
       derivable with other core rules such as KDuplicate, KConstruct.
       Few constructors and many parameters to ease formal verification of
       checkers.
 *)

exception Elaboration_failed

let t_open_quant_one q tq = match t_open_quant tq with
  | vs::vsl, trg, t_open ->
      let nt = t_quant q (t_close_quant vsl trg t_open) in
      vs, nt
  | _ -> raise Elaboration_failed

let elaborate init_ct c =
  let find_formula s pr cta = find_formula s pr.pr_name cta in
  let add pr t cta = add pr.pr_name t cta in
  let remove pr cta = remove pr.pr_name cta in
  let remove_var ls cta = remove_var ls.ls_name cta in
  let rec elaborate (map : term Mid.t) (cta : term ctask) (c : sc) : wkc =
    (* the map argument registers Let-defined variables and is used
       to substitute user-provided terms that appear in certificates *)
    let elab = elaborate map in
    match c with
    | Nc -> eprintf "No certificates@.";
            raise Elaboration_failed
    | Hole task -> KHole task
    | Axiom (i1, i2) ->
        let t1, pos1 = try find_formula "Axiom1" i1 cta
                       with e -> pcta err_formatter cta; raise e
        in
        let t2, pos2 = try find_formula "Axiom2" i2 cta
                       with e -> pcta err_formatter cta; raise e
        in
        assert (pos1 <> pos2);
        assert (t_equal t1 t2);
        let i1, i2 = if pos2 then i1, i2 else i2, i1 in
        KAxiom (t1, i1, i2)
    | Trivial i ->
        let t, pos = find_formula "Trivial" i cta in
        begin match t.t_node, pos with
        | Tapp (e, [t1; t2]), _ when t_equal t1 t2 && ls_equal e ps_equ ->
            KEqRefl (t1.t_ty, t1, i)
        | Tfalse, false | Ttrue, true ->
            KTrivial (pos, i)
        | _ -> eprintf "not an equality or not same terms in eqrefl";
               raise Elaboration_failed end
    | EqSym (i, c) ->
        let t, pos = find_formula "EqSym" i cta in
        begin match t.t_node with
        | Tapp (e, [t1; t2]) when ls_equal e ps_equ ->
            let rev_eq = t_app ps_equ [t2; t1] t.t_ty in
            let cta = add i (rev_eq, pos) cta in
            KEqSym (pos, t1.t_ty, t1, t2, i, elab cta c)
        | _ -> eprintf "not an equality"; raise Elaboration_failed end
    | EqTrans (i1, i2, i3, c) ->
        let t1, pos1 = find_formula "EqTrans" i1 cta in
        let t2, pos2 = find_formula "EqTrans" i2 cta in
        begin match t1.t_node, t2.t_node, pos1, pos2 with
        | Tapp (e1, [t11; t12]),
          Tapp (e2, [t21; t22]), false, false
            when t_equal t12 t21 && ls_equal e1 ps_equ && ls_equal e2 ps_equ ->
            let new_eq = t_app ps_equ [t11; t22] t1.t_ty in
            let cta = add i3 (new_eq, false) cta in
            KEqTrans (t11.t_ty, t11, t12, t22, i1, i2, i3, elab cta c)
        | _ -> eprintf "wrong hyps form in eqtrans";
               raise Elaboration_failed end
    | Assert (i, a, c1, c2) ->
        let a = a map in
        let cta1 = add i (a, true) cta in
        let cta2 = add i (a, false) cta in
        let c1 = elab cta1 c1 in
        let c2 = elab cta2 c2 in
        KAssert (i, a, c1, c2)
    | Let (x, i, c) ->
        let y, _ = find_formula "Let" i cta in
        let ix = match x.t_node with
          | Tapp (ls, []) -> ls.ls_name
          | _ -> assert false in
        let map = Mid.add ix y map in
        elaborate map cta c
    | Unfold (i, c) ->
        let t, pos = find_formula "Unfold" i cta in
        begin match t.t_node with
        | Tbinop (Tiff, t1, t2) ->
            let unfolded_iff = t_binary Tand
                                 (t_binary Timplies t1 t2)
                                 (t_binary Timplies t2 t1), pos in
            let cta = add i unfolded_iff cta in
            KUnfoldIff (pos, t1, t2, i, elab cta c)
        | Tbinop (Timplies, t1, t2) ->
            let unfolded_imp = t_binary Tor (t_not t1) t2, pos in
            let cta = add i unfolded_imp cta in
            KUnfoldArr (pos, t1, t2, i, elab cta c)
        | _ -> eprintf "Nothing to unfold";
               raise Elaboration_failed end
    | Fold (i, c) ->
        let t, pos = find_formula "Fold" i cta in
        begin match t.t_node with
        | Tbinop (Tand, {t_node = Tbinop (Timplies, t1, t2)},
                  {t_node = Tbinop (Timplies, t2', t1')})
            when t_equal t1 t1' && t_equal t2 t2' ->
            let folded_iff = t_binary Tiff t1 t2, pos in
            let cta = add i folded_iff cta in
            KFoldIff (pos, t1, t2, i, elab cta c)
        | Tbinop (Tor, {t_node = Tnot t1}, t2) ->
            let cta = add i (t_binary Timplies t1 t2, pos) cta in
            KFoldArr (pos, t1, t2, i, elab cta c)
        | _ -> eprintf "Nothing to fold";
               raise Elaboration_failed end
    | Split (i, c1, c2) ->
        let t, pos = find_formula "Split" i cta in
        let t1, t2 = match t.t_node, pos with
          | Tbinop (Tand, t1, t2), true
          | Tbinop (Tor, t1, t2), false -> t1, t2
          | _ -> eprintf "Not splittable@.";
                 raise Elaboration_failed in
        let cta1 = add i (t1, pos) cta in
        let cta2 = add i (t2, pos) cta in
        let c1 = elab cta1 c1 in
        let c2 = elab cta2 c2 in
        KSplit (pos, t1, t2, i, c1, c2)
    | Destruct (i, i1, i2, c) ->
        let t, pos = find_formula "Destruct" i cta in
        let t1, t2 = match t.t_node, pos with
          | Tbinop (Tand, t1, t2), false
          | Tbinop (Tor, t1, t2), true -> t1, t2
          | _ -> eprintf "Nothing to destruct@.";
                 raise Elaboration_failed in
        let cta = remove i cta
                  |> add i1 (t1, pos)
                  |> add i2 (t2, pos) in
        KDestruct (pos, t1, t2, i, i1, i2, elab cta c)
    | Construct (i1, i2, i, c) ->
        let t1, pos1 = find_formula "Construct1" i1 cta in
        let t2, pos2 = find_formula "Construct2" i2 cta in
        assert (pos1 = pos2);
        let t = if pos1
                then t_binary Tor t1 t2
                else t_binary Tand t1 t2 in
        let cta = remove i1 cta
                  |> remove i2
                  |> add i (t, pos1) in
        KConstruct (pos1, t1, t2, i1, i2, i, elab cta c)
    | Swap (i, c) ->
        let t, pos = find_formula "Swap" i cta in
        let neg, underlying_t, neg_t = match t.t_node with
          | Tnot t -> true, t, t
          | _ -> false, t, t_not t in
        let cta = add i (neg_t, not pos) cta in
        let pack = pos, underlying_t, i, elab cta c in
        if neg
        then KSwapNeg pack
        else KSwap pack
    | Clear (i, c) ->
        let t, pos = find_formula "Clear" i cta in
        let cta = remove i cta in
        KClear (pos, t, i, elab cta c)
    | Forget (i, c) ->
        let cta = remove_var i cta in
        KForget (i, elab cta c)
    | Duplicate (i1, i2, c) ->
        let t, pos = find_formula "Duplicate" i1 cta in
        let cta = add i2 (t, pos) cta in
        KDuplicate (pos, t, i1, i2, elab cta c)
    | IntroQuant (i, ls, c) ->
        let y = t_app_infer ls [] in
        let t, pos = find_formula "IntroQuant" i cta in
        begin match t.t_node with
          | Tquant (q, tq) ->
              let ty_opt = ls.ls_value in
              let vs, t_open = t_open_quant_one q tq in
              let t_applied = t_subst_single vs y t_open in
              let t_fun = t_eps (t_close_bound vs t_open) in
              let cta = add i (t_applied, pos) cta
                        |> add_var ls.ls_name (abstract_otype ty_opt) in
              KIntroQuant (pos, ty_opt, t_fun, i, ls, elab cta c)
          | _ -> raise Elaboration_failed end
    | InstQuant (i1, i2, t_inst, c) ->
        let t, pos = find_formula "InstQuant" i1 cta in
        begin match t.t_node with
          | Tquant (q, tq) ->
              let vs, t_open = t_open_quant_one q tq in
              let t_applied = t_subst_single vs t_inst t_open in
              let t = t_eps (t_close_bound vs t_open) in
              let cta = add i2 (t_applied, pos) cta in
              KInstQuant (pos, Some vs.vs_ty, t, i1, i2, t_inst, elab cta c)
          | _ -> eprintf "trying to instantiate a non-quantified hypothesis@.";
                 raise Elaboration_failed end
    | Rewrite (i1, i2, c) ->
        let rew_hyp, _ = find_formula "Finding rewrite hypothesis" i1 cta in
        let a, b, is_eq = match rew_hyp.t_node with
          | Tbinop (Tiff, a, b) -> a, b, false
          | Tapp (f, [a; b]) when ls_equal f ps_equ && a.t_ty <> None ->
              a, b, true
          | _ -> eprintf "Bad rewrite hypothesis@.";
                 raise Elaboration_failed in
        let t, pos = find_formula "Finding to be rewritten goal" i2 cta in
        let cta = add i2 (t_replace a b t, pos) cta in
        let c = elab cta c in
        let id = id_fresh "ctxt_var" in
        if is_eq
        then
          let ty = Opt.get a.t_ty in
          let vs = create_vsymbol id ty in
          let vst = t_var vs in
          let ctxt = t_eps (t_close_bound vs (t_replace a vst t)) in
          KRewrite (pos, None, Some ty, a, b, ctxt, i1, i2, c)
        else
          let t_r = t_app (create_psymbol id []) [] None in
          let ctxt = t_replace a t_r t in
          KRewrite (pos, Some t_r, None, a, b, ctxt, i1, i2, c)

    | Induction (g, hi1, hi2, hr, x, a, c1, c2) ->
        let a = a map in
        let le = cta.get_ls le_str in
        let lt = cta.get_ls lt_str in
        let t, _ = find_formula "induction" g cta in
        let vsx = create_vsymbol (id_fresh "ctxt_var_induction") ty_int in
        let ctxt = t_eps (t_close_bound vsx (t_replace x (t_var vsx) t)) in
        let cta1 = add hi1 (t_app le [x; a] None, false) cta in
        let vsn = create_vsymbol (id_fresh "ctxt_var") ty_int in
        let n = t_var vsn in
        let cta2 = add hi2 (t_app lt [a; x] None, false) cta
                   |> add hr (t_quant Tforall
                                (t_close_quant [vsn] []
                                   (t_binary Timplies
                                      (t_app lt [n; a] None)
                                      (t_replace x n t))),
                              false) in
        KInduction (g, hi1, hi2, hr, x, a, ctxt, elab cta1 c1, elab cta2 c2)
  in
  elaborate Mid.empty init_ct c

let eaxiom pos t i1 i2 =
  if pos then KAxiom (t, i1, i2)
  else KAxiom (t, i2, i1)
(* eaxiom true t i1 i2 ⇓ (Γ, i1 : t ⊢ Δ, i2 : t) stands *)
(* eaxiom false t i1 i2 ⇓ (Γ, i2 : t ⊢ Δ, i1 : t) stands *)

let eduplicate pos t i1 i2 c =
  let c_closed = eaxiom (not pos) t i1 i2 in
  let c1, c2 = if pos
               then c, c_closed
               else c_closed, c in
  KAssert (i2, t, c1, c2)

let erename pos a i1 i2 c =
  eduplicate pos a i1 i2 (KClear (pos, a, i1, c))

let rec trim c =
  match c with
  | KDuplicate (pos, t, i1, i2, c) ->
      let c = trim c in
      eduplicate pos t i1 i2 c
  | KConstruct (pos, t1, t2, i1, i2, i, c) ->
      let c = trim c in
      let i1' = id_register (id_fresh "i1") in
      let i2' = id_register (id_fresh "i2") in
      let c_open = KClear (pos, t1, i1', KClear (pos, t2, i2', c)) in
      let c_closed = KSplit (not pos, t1, t2, i,
                             eaxiom (not pos) t1 i1' i,
                             eaxiom (not pos) t2 i2' i) in
      let c1, c2, cut = if pos
                        then c_open, c_closed, CTbinop (Tor, t1, t2)
                        else c_closed, c_open, CTbinop (Tand, t1, t2) in
      erename pos t1 i1 i1' @@
        erename pos t2 i2 i2' @@
          KAssert (i, cut, c1, c2)
  | KFoldArr (pos, t1, t2, i, c') | KFoldIff (pos, t1, t2, i, c') ->
      let is_arr = match c with KFoldArr _ -> true | _ -> false in
      let c = trim c' in
      let j = id_register (id_fresh "fold_temp") in
      let pre, post = if is_arr
                      then CTbinop (Tor, CTnot t1, t2),
                           CTbinop (Timplies, t1, t2)
                      else CTbinop (Tand, CTbinop (Timplies, t1, t2),
                                    CTbinop (Timplies, t2, t1)),
                           CTbinop (Tiff, t1, t2) in
      let unfold pack = if is_arr then KUnfoldArr pack else KUnfoldIff pack in
      let c_open = KClear (pos, pre, j, c) in
      let c_closed = unfold (not pos, t1, t2, i, eaxiom pos pre i j) in
      let c1, c2 = if pos then c_open, c_closed else c_closed, c_open in
      erename pos pre i j @@
        KAssert (i, post, c1, c2)
  | KEqSym (pos, cty, t1, t2, i, c) ->
      let c = trim c in
      let j = id_register (id_fresh "eqsym_temp") in
      let pre = CTapp (CTapp (eq cty, t1), t2) in
      let post = CTapp (CTapp (eq cty, t2), t1) in
      let c_open = KClear (pos, pre, j, c) in
      let h, g, a, b = if pos then i, j, t2, t1 else j, i, t1, t2 in
      (* We want to close a task of the form <Γ, h : a = b ⊢ Δ, g : b = a> *)
      let ctxt = CTquant (CTlambda, cty, CTapp (CTapp (eq cty, b), CTbvar 0)) in
      let c_closed = KRewrite (not pos, None, cty, a, b, ctxt, h, g,
                               KEqRefl (cty, b, g)) in
      let c1, c2 = if pos then c_open, c_closed else c_closed, c_open in
      erename pos pre i j @@
        KAssert (i, post, c1, c2)
  | KEqTrans (cty, t1, t2, t3, i1, i2, i3, c) ->
      let c = trim c in
      let ctxt = CTquant (CTlambda, cty, CTapp (CTapp (eq cty, t1), CTbvar 0)) in
      eduplicate false (CTapp (CTapp (eq cty, t1), t2)) i1 i3 @@
        KRewrite (false, None, cty, t2, t3, ctxt, i2, i3, c)
  | _ -> map_kc trim (fun v -> v) (fun h -> h) (fun t -> t) (fun ty -> ty) c

let make_kernel_cert init_ct res_ct (c : scert) : kcert =
  fill_tasks c res_ct
  |> elaborate init_ct
  |> abstract_terms_types
  |> trim

