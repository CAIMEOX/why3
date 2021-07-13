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

type sc =
  | Nc
  | Hole of cterm ctask
  (* You should never use the Hole certificate *)
  | Assert of prsymbol * (term Mid.t -> term) * sc * sc
  | Let of term * prsymbol * sc
  | Axiom of prsymbol * prsymbol
  | Trivial of prsymbol
  | EqSym of prsymbol * sc
  | EqTrans of prsymbol * prsymbol * prsymbol * sc
  | Unfold of prsymbol * sc
  | Fold of prsymbol * sc
  | Split of prsymbol * sc * sc
  | Destruct of prsymbol * prsymbol * prsymbol * sc
  | Construct of prsymbol * prsymbol * prsymbol * sc
  | Swap of prsymbol * sc
  | Clear of prsymbol * sc
  | Forget of lsymbol * sc
  | Duplicate of prsymbol * prsymbol * sc
  | IntroQuant of prsymbol * lsymbol * sc
  | InstQuant of prsymbol * prsymbol * term * sc
  | Rewrite of prsymbol * prsymbol * sc
  | Induction of prsymbol * prsymbol * prsymbol * prsymbol * term *
                   (term Mid.t -> term) * sc * sc
  | Reduce of prsymbol * term * sc

type scert = int * (sc list -> sc)

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
   by negating it, removing a double negation after that *)
let clear p = newcert1 (fun a -> Clear (p, a))
(* Removes a premise p from the task *)
let forget ls = newcert1 (fun a -> Forget (ls, a))
(* Removes an unused variable ls from the task *)
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
let reduce p t' =
  newcert1 (fun a -> Reduce (p, t', a))
(* Returns the task where a computation has been done in p, changing it to t' *)

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

(* We will denote a ctask <{sigma; gamma_delta}> by <Σ | Γ ⊢ Δ>
   We sometimes omit the signature (when it's not confusing) and write <Γ ⊢ Δ> *)

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
  (* KClear (true, t, p, c) ⇓ (Γ ⊢ Δ, p : t) ≜ c ⇓ (Γ ⊢ Δ) *)
  (* KClear (false, t, p, c) ⇓ (Γ, p : t ⊢ Δ) ≜ c ⇓ (Γ ⊢ Δ) *)
  | KDuplicate of bool * 't * 'h * 'h * ('v, 'h, 't, 'ty) kc
  (* not kernel *)
  | KForget of 'v * ('v, 'h, 't, 'ty) kc
  (* KForget (v, c) ⇓ (Σ, v : τ | Γ ⊢ Δ) ≜ c ⇓ (Γ ⊢ Δ) *)
  | KAssert of 'h * 't * ('v, 'h, 't, 'ty) kc * ('v, 'h, 't, 'ty) kc
  (* KAssert (p, t, c₁, c₂) ⇓ (Γ ⊢ Δ) ≜
     c₁ ⇓ (Γ ⊢ Δ, p : t) and
     c₂ ⇓ (Γ, p : t ⊢ Δ) *)
  | KAxiom of 't * 'h * 'h
  (* KAxiom (t, p₁, p2) ⇓ (Γ, p₁ : t ⊢ Δ, p₂ : t) stands *)
  | KTrivial of bool * 'h
  (* KTrivial (false, p) ⇓ (Γ, p : ⊥ ⊢ Δ) stands *)
  (* KTrivial (true, p) ⇓ (Γ ⊢ Δ, p : ⊤) stands *)
  | KSwap of (bool * 't * 'h * ('v, 'h, 't, 'ty) kc)
  (* KSwap (false, t, p, c) ⇓ (Γ, p : t ⊢ Δ) ≜ c ⇓ (Γ ⊢ Δ, p : ¬t) *)
  (* KSwap (true, t, p, c) ⇓ (Γ ⊢ Δ, p : t) ≜ c ⇓ (Γ, p : ¬t ⊢ Δ) *)
  | KSwapNeg of (bool * 't * 'h * ('v, 'h, 't, 'ty) kc)
  (* not kernel *)
  | KUnfoldIff of (bool * 't * 't * 'h * ('v, 'h, 't, 'ty) kc)
  (* KUnfoldIff (false, t₁, t₂, p, c) ⇓ (Γ, p : t₁ ↔ t₂ ⊢ Δ) ≜
     c ⇓ (Γ, p : (t₁ → t₂) ∧ (t₂ → t₁) ⊢ Δ) *)
  (* KUnfoldIff (true, t₁, t₂, p, c) ⇓ (Γ ⊢ Δ, p : t₁ ↔ t₂) ≜
     c ⇓ (Γ ⊢ Δ, p : (t₁ → t₂) ∧ (t₂ → t₁)) *)
  | KUnfoldArr of (bool * 't * 't * 'h * ('v, 'h, 't, 'ty) kc)
  (* KUnfoldArr (false, t₁, t₂, p, c) ⇓ (Γ, p : t₁ → t₂ ⊢ Δ) ≜
     c ⇓ (Γ, p : ¬t₁ ∨ t₂ ⊢ Δ)*)
  (* KUnfoldArr (true, t₁, t₂, p, c) ⇓ (Γ ⊢ Δ, p : t₁ → t₂) ≜
     c ⇓ (Γ ⊢ Δ, p : ¬t₁ ∨ t₂)*)
  | KFoldIff of (bool * 't * 't * 'h * ('v, 'h, 't, 'ty) kc)
  (* not kernel *)
  | KFoldArr of (bool * 't * 't * 'h * ('v, 'h, 't, 'ty) kc)
  (* not kernel *)
  | KSplit of bool * 't * 't * 'h * ('v, 'h, 't, 'ty) kc * ('v, 'h, 't, 'ty) kc
  (* KSplit (false, t₁, t₂, p, c₁, c₂) ⇓ (Γ, p : t₁ ∨ t₂ ⊢ Δ) ≜
     c₁ ⇓ (Γ, p : t₁ ⊢ Δ) and
     c₂ ⇓ (Γ, p : t₂ ⊢ Δ) *)
  (* KSplit (true, t₁, t₂, p, c₁, c₂) ⇓ (Γ ⊢ Δ, p : t₁ ∧ t₂) ≜
     c₁ ⇓ (Γ ⊢ Δ, p : t₁) and
     c₂ ⇓ (Γ ⊢ Δ, p : t₂) *)
  | KDestruct of bool * 't * 't * 'h * 'h * 'h * ('v, 'h, 't, 'ty) kc
  (* KDestruct (false, t₁, t₂, p, p₁, p₂, c) ⇓ (Γ, p : t₁ ∧ t₂ ⊢ Δ) ≜
     c ⇓ (Γ, p₁ : t₁, p₂ : t₂ ⊢ Δ) *)
  (* KDestruct (true, t₁, t₂, p, p₁, p₂, c) ⇓ (Γ ⊢ Δ, p : t₁ ∨ t₂) ≜
     c ⇓ (Γ ⊢ Δ, p₁ : t₁, p₂ : t₂) *)
  | KConstruct of bool * 't * 't * 'h * 'h * 'h * ('v, 'h, 't, 'ty) kc
  (* not kernel *)
  | KIntroQuant of bool * 'ty * 't * 'h * 'v * ('v, 'h, 't, 'ty) kc
  (* KIntroQuant (false, τ, f, p, y, c) ⇓ (Σ | Γ, p : ∃ x : τ. f ⊢ Δ) ≜
     c ⇓ (Σ, y : τ | Γ, p : f[x ↦ y] ⊢ Δ)
     and y ∉ Σ *)
  (* KIntroQuant (true, τ, f, p, y, c) ⇓ (Σ | Γ ⊢ Δ, p : ∀ x : τ. f) ≜
     c ⇓ (Σ, y : τ | Γ ⊢ Δ, p : f[x ↦ y])
     and y ∉ Σ *)
  | KInstQuant of bool * 'ty * 't * 'h * 'h * 't * ('v, 'h, 't, 'ty) kc
  (* KInstQuant (false, τ, f, p₁, p₂, t, c) ⇓ (Σ | Γ, p₁ : ∀ x : τ. f ⊢ Δ) ≜
     c ⇓ (Σ | Γ, p₁ : ∀ x : τ. f, p₂ : f[x ↦ t] ⊢ Δ)
     and Σ ⊩ t : τ *)
  (* KInstQuant (true, τ, f, p₁, p₂, t, c) ⇓ (Σ | Γ ⊢ Δ, p₁ : ∃ x : τ. f) ≜
     c ⇓ (Σ | Γ ⊢ Δ, p₁ : ∃ x : τ. f, p₂ : f[x ↦ t])
     and Σ ⊩ t : τ *)
  | KEqRefl of 'ty * 't * 'h
  (* KEqRefl (τ, t, g) ⇓ (Γ ⊢ Δ, g : t = t) stands *)
  | KEqSym of bool * 'ty * 't * 't * 'h * ('v, 'h, 't, 'ty) kc
  (* not kernel *)
  | KEqTrans of 'ty * 't * 't * 't * 'h * 'h * 'h * ('v, 'h, 't, 'ty) kc
  (* not kernel *)
  | KRewrite of bool * 't option * 'ty * 't * 't * 't * 'h * 'h
                * ('v, 'h, 't, 'ty) kc
  (* KRewrite (true, None, τ, t₁, t₂, f, h, p, c) ⇓
     (Γ, h : t₁ = t₂ ⊢ Δ, p : f[t₁]) ≜
     c ⇓ (Γ, h : t₁ = t₂ ⊢ Δ, p : f[t₂]) *)
  (* KRewrite (false, None, τ, t₁, t₂, f, h, p, c) ⇓
     (Γ, h : t₁ = t₂, p : f[t₁] ⊢ Δ) ≜
     c ⇓ (Γ, h : t₁ = t₂, p : f[t₂] ⊢ Δ) *)
  (* KRewrite (true, Some _, τ, t₁, t₂, f, h, p, c) ⇓
     (Γ, h : t₁ ↔ t₂ ⊢ Δ, p : f[t₁]) ≜
     c ⇓ (Γ, h : t₁ ↔ t₂ ⊢ Δ, p : f[t₂]) *)
  (* KRewrite (false, Some _, τ, t₁, t₂, f, h, p, c) ⇓
     (Γ, h : t₁ ↔ t₂, p : f[t₁] ⊢ Δ) ≜
     c ⇓ (Γ, h : t₁ ↔ t₂, p : f[t₂] ⊢ Δ) *)
  | KInduction of 'h * 'h * 'h * 'h * 't * 't * 't
                  * ('v, 'h, 't, 'ty) kc * ('v, 'h, 't, 'ty) kc
(* KInduction (G, Hi₁, Hi₂, Hr, x, a, f, c₁, c₂) ⇓ (Γ ⊢ Δ, G : f[x]) ≜
   c₁ ⇓ (Γ, Hi₁ : i ≤ a ⊢ Δ, G : f[x]) and
   c₂ ⇓ (Γ, Hi₂ : a < i, Hr: ∀ n : int. n < i → f[n] ⊢ f[x])
   and i does not appear in Γ, Δ or C
   and x and a are of type int *)
(* In the induction and rewrite rules f is a context and the notation f[t]
   stands for this context where the holes have been replaced with t *)
  | KReduce of bool * 't * 't * 'h * ('v, 'h, 't, 'ty) kc
  (* KReduce (false, t, t', p, c) ⇓ (Γ, p : t ⊢ Δ) ≜
     c ⇓ (Γ, p : t' ⊢ Δ)
     and t ≡ t'
     KReduce (true, t, t', p, c)  ⇓ (Γ ⊢ Δ, p : t) ≜
     c ⇓ (Γ ⊢ Δ, p : t')
     and t ≡ t' *)

(* Why3 kernel certificates *)
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
  | Assert (p, _, c1, c2) ->
      fprintf fmt "Assert (@[%a, <fun>,@ @[<4>%a@],@ @[<4>%a@])@]"
        prpr p prc c1 prc c2
  | Let (x, p, c) -> fprintf fmt "Let (%a, %a,@ %a)" prt x prpr p prc c
  | Axiom (p1, p2) -> fprintf fmt "Axiom (%a, %a)" prpr p1 prpr p2
  | Trivial p -> fprintf fmt "Trivial %a" prpr p
  | EqSym (p, c) -> fprintf fmt "EqSym (%a,@ %a)" prpr p prc c
  | EqTrans (p1, p2, p3, c) -> fprintf fmt "EqTrans (%a, %a, %a, @ %a)"
                                 prpr p1 prpr p2 prpr p3 prc c
  | Unfold (p, c) -> fprintf fmt "Unfold (%a,@ %a)" prpr p prc c
  | Fold (p, c) -> fprintf fmt "Fold (%a,@ %a)" prpr p prc c
  | Split (p, c1, c2) -> fprintf fmt "Split (@[%a,@ @[<4>%a@],@ @[<4>%a@])@]"
                           prpr p prc c1 prc c2
  | Destruct (p, p1, p2, c) ->
      fprintf fmt "Destruct (%a, %a, %a,@ %a)" prpr p prpr p1 prpr p2 prc c
  | Construct (p1, p2, p, c) ->
      fprintf fmt "Construct (%a, %a, %a,@ %a)" prpr p1 prpr p2 prpr p prc c
  | Swap (p, c) -> fprintf fmt "Swap (%a,@ %a)" prpr p prc c
  | Clear (p, c) -> fprintf fmt "Clear@ (%a,@ %a)" prpr p prc c
  | Forget (v, c) -> fprintf fmt "Forget@ (%a,@ %a)" prls v prc c
  | Duplicate (p1, p2, c) -> fprintf fmt "Duplicate@ (%a, %a, @ %a)"
                               prpr p1 prpr p2 prc c
  | IntroQuant (p, y, c) -> fprintf fmt "IntroQuant (%a, %a,@ %a)"
                              prpr p prls y prc c
  | InstQuant (p1, p2, t, c) -> fprintf fmt "InstQuant (%a, %a, %a,@ %a)"
                                prpr p1 prpr p2 prt t prc c
  | Rewrite (p, h, c) -> fprintf fmt "Rewrite (%a, %a,@ %a)" prpr p prpr h prc c
  | Induction (p1, p2, p3, p4, x, _, c1, c2) ->
      fprintf fmt "Induction (%a, %a, %a, %a, %a, <fun>,@ %a,@ %a)"
        prpr p1 prpr p2 prpr p3 prpr p4 prt x prc c1 prc c2
  | Reduce (p, t, c) -> fprintf fmt "Reduce@ (%a,@ %a,@ %a)" prpr p prt t prc c

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
  | Trivial p -> Trivial p
  | EqSym (p, c) -> EqSym (p, fc c)
  | EqTrans (p1, p2, p3, c) -> EqTrans (p1, p2, p3, fc c)
  | Assert (p, t, c1, c2) ->
      let f1 = fc c1 in
      let f2 = fc c2 in
      Assert (p, t, f1, f2)
  | Let (x, p, c) -> Let (x, p, fc c)
  | Unfold (p, c) -> Unfold (p, fc c)
  | Fold (p, c) -> Fold (p, fc c)
  | Split (p, c1, c2) ->
      let f1 = fc c1 in let f2 = fc c2 in
                        Split (p, f1, f2)
  | Destruct (p, p1, p2, c) -> Destruct (p, p1, p2, fc c)
  | Construct (p1, p2, p, c) -> Construct (p1, p2, p, fc c)
  | Swap (p, c) -> Swap (p, fc c)
  | Clear (p, c) -> Clear (p, fc c)
  | Forget (v, c) -> Forget (v, fc c)
  | Duplicate (p1, p2, c) -> Duplicate (p1, p2, fc c)
  | IntroQuant (p, y, c) -> IntroQuant (p, y, fc c)
  | InstQuant (p1, p2, t, c) -> InstQuant (p1, p2, t, fc c)
  | Rewrite (p, h, c) -> Rewrite (p, h, fc c)
  | Induction (p1, p2, p3, p4, x, a, c1, c2) ->
      Induction (p1, p2, p3, p4, x, a, fc c1, fc c2)
  | Reduce (p, t, c) -> Reduce (p, t, fc c)

(* To define recursive functions on elements of type kc *)
let map_kc fc fv fh ft fty = function
  | KHole _ as c -> c
  | KAssert (p, t, c1, c2) ->
      let f1 = fc c1 in
      let f2 = fc c2 in
      KAssert (fh p, ft t, f1, f2)
  | KAxiom (t, p1, p2) -> KAxiom (ft t, fh p1, fh p2)
  | KTrivial (pos, p) -> KTrivial (pos, fh p)
  | KEqRefl (ty, t, g) -> KEqRefl (fty ty, ft t, fh g)
  | KEqSym (pos, ty, t1, t2, p, c) ->
      KEqSym (pos, fty ty, ft t1, ft t2, fh p, fc c)
  | KEqTrans (ty, t1, t2, t3, p1, p2, p3, c) ->
      KEqTrans (fty ty, ft t1, ft t2, ft t3, fh p1, fh p2, fh p3, fc c)
  | KSplit (pos, t1, t2, p, c1, c2) ->
      let f1 = fc c1 in
      let f2 = fc c2 in
      KSplit (pos, ft t1, ft t2, fh p, f1, f2)
  | KUnfoldIff (pos, t1, t2, p, c) -> KUnfoldIff (pos, ft t1, ft t2, fh p, fc c)
  | KUnfoldArr (pos, t1, t2, p, c) -> KUnfoldArr (pos, ft t1, ft t2, fh p, fc c)
  | KFoldIff (pos, t1, t2, p, c) -> KFoldIff (pos, ft t1, ft t2, fh p, fc c)
  | KFoldArr (pos, t1, t2, p, c) -> KFoldArr (pos, ft t1, ft t2, fh p, fc c)
  | KDestruct (pos, t1, t2, p, j1, j2, c) ->
      KDestruct (pos, ft t1, ft t2, fh p, fh j1, fh j2, fc c)
  | KConstruct (pos, t1, t2, p1, p2, j, c) ->
      KConstruct (pos, ft t1, ft t2, fh p1, fh p2, fh j, fc c)
  | KSwap (pos, t, p, c) -> KSwap (pos, ft t, fh p, fc c)
  | KSwapNeg (pos, t, p, c) -> KSwapNeg (pos, ft t, fh p, fc c)
  | KClear (pos, t, p, c) -> KClear (pos, ft t, fh p, fc c)
  | KForget (p, c) -> KForget (fv p, fc c)
  | KDuplicate (pos, t, p1, p2, c) -> KDuplicate (pos, ft t, fh p1, fh p2, fc c)
  | KIntroQuant (pos, ty, f, p, y, c) ->
      KIntroQuant (pos, fty ty, ft f, fh p, fv y, fc c)
  | KInstQuant (pos, ty, f, p1, p2, t, c) ->
      KInstQuant (pos, fty ty, ft f, fh p1, fh p2, ft t, fc c)
  | KRewrite (pos, topt, ty, t1, t2, f, p, h, c) ->
      KRewrite (pos, Opt.map ft topt, fty ty, ft t1, ft t2, ft f, fh p, fh h, fc c)
  | KInduction (p1, p2, p3, p4, x, a, f, c1, c2) ->
      KInduction (fh p1, fh p2, fh p3, fh p4, ft x, ft a, ft f, fc c1, fc c2)
  | KReduce (pos, t, t', p, c) -> KReduce (pos, ft t, ft t',fh p, fc c)

(** Compile chain.
    1. surface certificates: scert
       The certificates returned by certifying transformations.
       Many constructors and few parameters to ease making certifying
       a transformation.
    2. applied certificates: sc
       Result of the function <fill_tasks>, this is not a function anymore and
       resulting tasks are contained in the certificate.
    3. elaborated certificates: wkc
       Result of the main elaboration function <elaborate> and as such contains
       many additional information such as the current formula and whether the focus
       is on a goal or on an hypothesis. Knowing those additional informations,
       Let-variables can be substituted
    4. abstracted kernel certificates: kcert
       Result of applying the <abstract_terms_types>. Same as before but with
       simpler symbols, terms and types that can be used by our checkers. It also
       builds the context to rewrite formulas since this is a function that cannot be
       defined as a Why3.term
    5. trimmed certificates: kcert
       Result of the function <trim>. It trims the certificate of rules that are
       derivable with other core rules such as KDuplicate, KConstruct.
       Few constructors and many parameters to ease formal verification of
       checkers.
 *)

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
    | Axiom (p1, p2) ->
        let t1, pos1 = try find_formula "Axiom1" p1 cta
                       with e -> pcta err_formatter cta; raise e
        in
        let t2, pos2 = try find_formula "Axiom2" p2 cta
                       with e -> pcta err_formatter cta; raise e
        in
        assert (pos1 <> pos2);
        assert (t_equal t1 t2);
        let p1, p2 = if pos2 then p1, p2 else p2, p1 in
        KAxiom (t1, p1, p2)
    | Trivial p ->
        let t, pos = find_formula "Trivial" p cta in
        begin match t.t_node, pos with
        | Tapp (e, [t1; t2]), _ when t_equal t1 t2 && ls_equal e ps_equ ->
            KEqRefl (t1.t_ty, t1, p)
        | Tfalse, false | Ttrue, true ->
            KTrivial (pos, p)
        | _ -> eprintf "not an equality or not same terms in eqrefl@.";
               raise Elaboration_failed end
    | EqSym (p, c) ->
        let t, pos = find_formula "EqSym" p cta in
        begin match t.t_node with
        | Tapp (e, [t1; t2]) when ls_equal e ps_equ ->
            let rev_eq = t_app ps_equ [t2; t1] t.t_ty in
            let cta = add p (rev_eq, pos) cta in
            KEqSym (pos, t1.t_ty, t1, t2, p, elab cta c)
        | _ -> eprintf "not an equality@.";
               raise Elaboration_failed end
    | EqTrans (p1, p2, i3, c) ->
        let t1, pos1 = find_formula "EqTrans" p1 cta in
        let t2, pos2 = find_formula "EqTrans" p2 cta in
        begin match t1.t_node, t2.t_node, pos1, pos2 with
        | Tapp (e1, [t11; t12]),
          Tapp (e2, [t21; t22]), false, false
            when t_equal t12 t21 && ls_equal e1 ps_equ && ls_equal e2 ps_equ ->
            let new_eq = t_app ps_equ [t11; t22] t1.t_ty in
            let cta = add i3 (new_eq, false) cta in
            KEqTrans (t11.t_ty, t11, t12, t22, p1, p2, i3, elab cta c)
        | _ -> eprintf "wrong hyps form in eqtrans@.";
               raise Elaboration_failed end
    | Assert (p, t, c1, c2) ->
        let t = t map in
        let cta1 = add p (t, true) cta in
        let cta2 = add p (t, false) cta in
        let c1 = elab cta1 c1 in
        let c2 = elab cta2 c2 in
        KAssert (p, t, c1, c2)
    | Let (x, p, c) ->
        let y, _ = find_formula "Let" p cta in
        let ix = match x.t_node with
          | Tapp (ls, []) -> ls.ls_name
          | _ -> assert false in
        let map = Mid.add ix y map in
        elaborate map cta c
    | Unfold (p, c) ->
        let t, pos = find_formula "Unfold" p cta in
        begin match t.t_node with
        | Tbinop (Tiff, t1, t2) ->
            let unfolded_iff = t_binary Tand
                                 (t_binary Timplies t1 t2)
                                 (t_binary Timplies t2 t1), pos in
            let cta = add p unfolded_iff cta in
            KUnfoldIff (pos, t1, t2, p, elab cta c)
        | Tbinop (Timplies, t1, t2) ->
            let unfolded_imp = t_binary Tor (t_not t1) t2, pos in
            let cta = add p unfolded_imp cta in
            KUnfoldArr (pos, t1, t2, p, elab cta c)
        | _ -> eprintf "Nothing to unfold@.";
               raise Elaboration_failed end
    | Fold (p, c) ->
        let t, pos = find_formula "Fold" p cta in
        begin match t.t_node with
        | Tbinop (Tand, {t_node = Tbinop (Timplies, t1, t2)},
                  {t_node = Tbinop (Timplies, t2', t1')})
            when t_equal t1 t1' && t_equal t2 t2' ->
            let folded_iff = t_binary Tiff t1 t2, pos in
            let cta = add p folded_iff cta in
            KFoldIff (pos, t1, t2, p, elab cta c)
        | Tbinop (Tor, {t_node = Tnot t1}, t2) ->
            let cta = add p (t_binary Timplies t1 t2, pos) cta in
            KFoldArr (pos, t1, t2, p, elab cta c)
        | _ -> eprintf "Nothing to fold@.";
               raise Elaboration_failed end
    | Split (p, c1, c2) ->
        let t, pos = find_formula "Split" p cta in
        let t1, t2 = match t.t_node, pos with
          | Tbinop (Tand, t1, t2), true
          | Tbinop (Tor, t1, t2), false -> t1, t2
          | _ -> eprintf "Not splittable@.";
                 raise Elaboration_failed in
        let cta1 = add p (t1, pos) cta in
        let cta2 = add p (t2, pos) cta in
        let c1 = elab cta1 c1 in
        let c2 = elab cta2 c2 in
        KSplit (pos, t1, t2, p, c1, c2)
    | Destruct (p, p1, p2, c) ->
        let t, pos = find_formula "Destruct" p cta in
        let t1, t2 = match t.t_node, pos with
          | Tbinop (Tand, t1, t2), false
          | Tbinop (Tor, t1, t2), true -> t1, t2
          | _ -> eprintf "Nothing to destruct@.";
                 raise Elaboration_failed in
        let cta = remove p cta
                  |> add p1 (t1, pos)
                  |> add p2 (t2, pos) in
        KDestruct (pos, t1, t2, p, p1, p2, elab cta c)
    | Construct (p1, p2, p, c) ->
        let t1, pos1 = find_formula "Construct1" p1 cta in
        let t2, pos2 = find_formula "Construct2" p2 cta in
        assert (pos1 = pos2);
        let t = if pos1
                then t_binary Tor t1 t2
                else t_binary Tand t1 t2 in
        let cta = remove p1 cta
                  |> remove p2
                  |> add p (t, pos1) in
        KConstruct (pos1, t1, t2, p1, p2, p, elab cta c)
    | Swap (p, c) ->
        let t, pos = find_formula "Swap" p cta in
        let neg, underlying_t, neg_t = match t.t_node with
          | Tnot t -> true, t, t
          | _ -> false, t, t_not t in
        let cta = add p (neg_t, not pos) cta in
        let pack = pos, underlying_t, p, elab cta c in
        if neg
        then KSwapNeg pack
        else KSwap pack
    | Clear (p, c) ->
        let t, pos = find_formula "Clear" p cta in
        let cta = remove p cta in
        KClear (pos, t, p, elab cta c)
    | Forget (v, c) ->
        let cta = remove_var v cta in
        KForget (v, elab cta c)
    | Duplicate (p1, p2, c) ->
        let t, pos = find_formula "Duplicate" p1 cta in
        let cta = add p2 (t, pos) cta in
        KDuplicate (pos, t, p1, p2, elab cta c)
    | IntroQuant (p, ls, c) ->
        let y = t_app_infer ls [] in
        let t, pos = find_formula "IntroQuant" p cta in
        begin match t.t_node with
          | Tquant (q, tq) ->
              let ty_opt = ls.ls_value in
              let vs, t_open = t_open_quant_one q tq in
              let t_applied = t_subst_single vs y t_open in
              let t_fun = t_eps (t_close_bound vs t_open) in
              let cta = add p (t_applied, pos) cta
                        |> add_var ls.ls_name (abstract_otype ty_opt) in
              KIntroQuant (pos, ty_opt, t_fun, p, ls, elab cta c)
          | _ -> eprintf "trying to introduce a non-quantified hypothesis@.";
                 raise Elaboration_failed end
    | InstQuant (p1, p2, t_inst, c) ->
        let t, pos = find_formula "InstQuant" p1 cta in
        begin match t.t_node with
          | Tquant (q, tq) ->
              let vs, t_open = t_open_quant_one q tq in
              let t_applied = t_subst_single vs t_inst t_open in
              let t = t_eps (t_close_bound vs t_open) in
              let cta = add p2 (t_applied, pos) cta in
              KInstQuant (pos, Some vs.vs_ty, t, p1, p2, t_inst, elab cta c)
          | _ -> eprintf "trying to instantiate a non-quantified hypothesis@.";
                 raise Elaboration_failed end
    | Rewrite (h, p, c) ->
        let rew_hyp, _ = find_formula "Finding rewrite hypothesis" h cta in
        let a, b, is_eq = match rew_hyp.t_node with
          | Tbinop (Tiff, a, b) -> a, b, false
          | Tapp (f, [a; b]) when ls_equal f ps_equ && a.t_ty <> None ->
              a, b, true
          | _ -> eprintf "Bad rewrite hypothesis@.";
                 raise Elaboration_failed in
        let t, pos = find_formula "Finding to be rewritten goal" p cta in
        let cta = add p (t_replace a b t, pos) cta in
        let c = elab cta c in
        let id = id_fresh "ctxt_var" in
        if is_eq
        then
          let ty = Opt.get a.t_ty in
          let vs = create_vsymbol id ty in
          let vst = t_var vs in
          let ctxt = t_eps (t_close_bound vs (t_replace a vst t)) in
          KRewrite (pos, None, Some ty, a, b, ctxt, h, p, c)
        else
          let t_r = t_app (create_psymbol id []) [] None in
          let ctxt = t_replace a t_r t in
          KRewrite (pos, Some t_r, None, a, b, ctxt, h, p, c)

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
    | Reduce (p, t', c) ->
        let t, pos = find_formula "Reduce" p cta in
        let cta = add p (t', pos) cta in
        KReduce (pos, t, t', p, elab cta c)
  in
  elaborate Mid.empty init_ct c

let kaxiom pos t p1 p2 =
  if pos then KAxiom (t, p1, p2)
  else KAxiom (t, p2, p1)
(* kaxiom true t p1 p2 ⇓ (Γ, p1 : t ⊢ Δ, p2 : t) stands *)
(* kaxiom false t p1 p2 ⇓ (Γ, p2 : t ⊢ Δ, p1 : t) stands *)

let kduplicate pos t p1 p2 c =
  let c_closed = kaxiom (not pos) t p1 p2 in
  let c1, c2 = if pos
               then c, c_closed
               else c_closed, c in
  KAssert (p2, t, c1, c2)
(* kduplicate true t p₁ p₂ c ⇓ (Γ ⊢ Δ, p₁ : t) ≜ c ⇓ (Γ ⊢ Δ, p₁ : t, p₂ : t) *)
(* kduplicate false t p₁ p₂ c ⇓ (Γ, p₁ : t ⊢ Δ) ≜ c ⇓ (Γ, p₁ : t, p₂ : t ⊢ Δ) *)

let krename pos t p1 p2 c =
  kduplicate pos t p1 p2 (KClear (pos, t, p1, c))
(* krename true t p₁ p₂ c ⇓ (Γ ⊢ Δ, p₁ : t) ≜ c ⇓ (Γ ⊢ Δ, p₂ : t) *)
(* krename false t p₁ p₂ c ⇓ (Γ, p₁ : t ⊢ Δ) ≜ c ⇓ (Γ, p₂ : t ⊢ Δ) *)

let kswapneg pos t p c =
  let q = id_register (id_fresh "q") in
  let c_closed = KSwap (pos, t, p, kaxiom pos (CTnot t) p q) in
  let c_open = KClear (pos, CTnot t, q, c) in
  let c1, c2 = if pos then c_closed, c_open else c_open, c_closed in
  krename pos (CTnot t) p q @@
    KAssert (p, t, c1, c2)
(* kswapneg false t p c ⇓ (Γ, p : ¬ t ⊢ Δ) ≜ c ⇓ (Γ ⊢ Δ, p : t)  *)
(* kswapneg true t i c ⇓ (Γ ⊢ Δ, p : ¬ t) ≜ c ⇓ (Γ, p : t ⊢ Δ)  *)

let kconstruct pos t1 t2 p1 p2 p c =
  let p1' = id_register (id_fresh "p1") in
  let p2' = id_register (id_fresh "p2") in
  let c_open = KClear (pos, t1, p1', KClear (pos, t2, p2', c)) in
  let c_closed = KSplit (not pos, t1, t2, p,
                         kaxiom pos t1 p p1',
                         kaxiom pos t2 p p2') in
  let c1, c2, cut = if pos
                    then c_open, c_closed, CTbinop (Tor, t1, t2)
                    else c_closed, c_open, CTbinop (Tand, t1, t2) in
  krename pos t1 p1 p1' @@
    krename pos t2 p2 p2' @@
      KAssert (p, cut, c1, c2)
(* kconstruct false t₁ t₂ p₁ p₂ p c ⇓ (Γ, p₁ : t₁, p₂ : t₂ ⊢ Δ) ≜
   c ⇓ (Γ, p : t₁ ∧ t₂ ⊢ Δ)  *)
(* kconstruct true t₁ t₂ p₁ p₂ p c ⇓ (Γ ⊢ Δ, p₁ : t₁, p₂ : t₂) ≜
   c ⇓ (Γ ⊢ Δ, p : t₁ ∨ t₂)  *)

let rec trim c =
  match c with
  | KDuplicate (pos, t, p1, p2, c) ->
      let c = trim c in
      kduplicate pos t p1 p2 c
  | KSwapNeg (pos, t, p, c) ->
      let c = trim c in
      kswapneg pos t p c
  | KConstruct (pos, t1, t2, p1, p2, p, c) ->
      let c = trim c in
      kconstruct pos t1 t2 p1 p2 p c
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
      let c_closed = unfold (not pos, t1, t2, i, kaxiom pos pre i j) in
      let c1, c2 = if pos then c_open, c_closed else c_closed, c_open in
      krename pos pre i j @@
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
      krename pos pre i j @@
        KAssert (i, post, c1, c2)
  | KEqTrans (cty, t1, t2, t3, i1, i2, i3, c) ->
      let c = trim c in
      let ctxt = CTquant (CTlambda, cty, CTapp (CTapp (eq cty, t1), CTbvar 0)) in
      kduplicate false (CTapp (CTapp (eq cty, t1), t2)) i1 i3 @@
        KRewrite (false, None, cty, t2, t3, ctxt, i2, i3, c)
  | _ -> map_kc trim (fun v -> v) (fun h -> h) (fun t -> t) (fun ty -> ty) c

let make_kernel_cert init_ct res_ct (c : scert) : kcert =
  fill_tasks c res_ct
  |> elaborate init_ct
  |> abstract_terms_types
  |> trim

