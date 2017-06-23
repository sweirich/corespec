(*************************************************************************)
(** A simple, typed language in Coq. *)
(*************************************************************************)

(** An interactive tutorial on developing programming language metatheory.
    This file uses the language of PFPL Ch. 4 (called E) to demonstrate the
    locally nameless representation of lambda terms and cofinite
    quantification in judgments.
    This tutorial concentrates on "how" to formalize languages; for more
    details about "why" we use this style of development see: "Engineering
    Formal Metatheory", Aydemir, Chargu'eraud, Pierce, Pollack, Weirich. POPL
    2008.
    Tutorial author: Stephanie Weirich Acknowledgement: based on a tutorial by
    Brian Aydemir and Stephanie Weirich, with help from Aaron Bohannon, Nate
    Foster, Benjamin Pierce, Jeffrey Vaughan, Dimitrios Vytiniotis, and Steve
    Zdancewic.  Adapted from code by Arthur Chargu'eraud.
*)


(*************************************************************************)
(** Background
     
     The tutorial starts gently and assumes only general knowledge of
     functional programming or programming language metatheory. It includes
     deeper explorations (marked below as Challenge Problems) suitable for
     those who have previously studied Software Foundations
     (https://www.cis.upenn.edu/~bcpierce/sf/current/toc.html). If you are 
     new to Coq, you should prove the challenge problems on paper as their
     proof scripts require more tactics than are presented here. 
*)
(*************************************************************************)


(** First, we import a number of definitions from the Metatheory library (see
    Metatheory.v).  This library is available from
    https://github.com/plclub/metalib.
    The following command makes those definitions available in the rest of
    this file.  This command will only succeed if you have already run "make"
    in the tutorial directory to compile the Metatheory library.  
  *)

Require Import Metatheory.

(* Some examples require strings, so we also include those. *)
Require Import Strings.String.

(*************************************************************************)
(** * Syntax of E *)
(*************************************************************************)

(** The concrete syntax of E looks something like this:
    Typ   tau  ::= num
                   string
    Exp   e    ::= x                      variable
                   n                      numeral
                   "s"                    string
                   e1 + e2                addition 
                   e1 * e2                multiplication
                   e1 ^ e2                concatenation
                   len (e)                length
                   let x be x1 in e2      definition 
    We use a locally nameless representation, where bound variables are
    represented as natural numbers (de Bruijn indices) and free variables are
    represented as [atom]s.  The type [atom], defined in the MetatheoryAtom
    library, represents names.  Equality on names is decidable
    ([eq_atom_dec]), and it is possible to generate an atom fresh for any
    given finite set of atoms ([atom_fresh]).  
 *)


Inductive typ : Set :=
  | typ_num     : typ
  | typ_string  : typ.

(* binary operators. *)
Inductive op : Set :=
  | plus
  | times
  | cat.

(* expressions of E *)
Inductive exp : Set :=
  (* bound and free variables *)
  | exp_bvar : nat  -> exp
  | exp_fvar : atom -> exp
  (* constants *)                        
  | exp_num  : nat -> exp                     
  | exp_str  : string -> exp
  (* binary operators *)                          
  | exp_op   : op -> exp -> exp -> exp
  (* skip length *)
  (* let expressions *)                                  
  | exp_let  : exp  -> exp -> exp.

(** For example, we can encode the expression 
      "let x be y + 1 in x" as below.
    Because "y" is free variable in this term, we need to assume an
    atom for this name.
*)

Parameter Y : atom.
Definition demo_rep1 :=
  exp_let (exp_op plus (exp_fvar Y) (exp_num 1)) (exp_bvar 0).

(** Below is another example: the encoding of 
     "let x be 1 in let y be 2 in x + y"
*)

Definition demo_rep2 :=
  exp_let (exp_num 1) (exp_let (exp_num 2) (exp_op plus (exp_bvar 0) (exp_bvar 1))).


(** *** Exercise [defns]
    Uncomment and then complete the definitions of the following
	 terms using the locally nameless representation.
       "one"     :   let x be let y be 1 in y in x
       "two"     :   let x be 1 in let y be x + 1 in y
       "three"   :   let x be y in let y be x in x + y
 
*)


Definition one := exp_let (exp_let (exp_num 1) (exp_bvar 0)) (exp_bvar 0).
   (* FILL IN HERE *)
Definition two := exp_let (exp_num 1) (exp_let (exp_op plus (exp_bvar 1) 
    (exp_num 1)) (exp_bvar 0)).
  (* FILL IN HERE *)
Definition three := exp_let (exp_fvar Y) (exp_let (exp_bvar 1) (exp_op plus 
    (exp_bvar 1) (exp_bvar 0))).
  (* FILL IN HERE *)


(** There are two important advantages of the locally nameless
    representation:
     - Alpha-equivalent terms have a unique representation.
       We're always working up to alpha-equivalence.
     - Operations such as free variable substitution and free
       variable calculation have simple recursive definitions
       (and therefore are simple to reason about).
    Weighed against these advantages are two drawbacks:
     - The [exp] datatype admits terms, such as 
       [let (exp_bvar 3) (exp_bvar 3)], where
       indices are unbound.
       A term is called "locally closed" when it contains
       no unbound indices.
     - We must define *both* bound variable & free variable
       substitution and reason about how these operations
       interact with each other.
*)


(*************************************************************************)
(** * Substitution *)
(*************************************************************************)

(** Substitution replaces a free variable with a term.  The definition
    below is simple for two reasons:
      - Because bound variables are represented using indices, there
        is no need to worry about variable capture.
      - We assume that the term being substituted in is locally
        closed.  Thus, there is no need to shift indices when
        passing under a binder.
*)

Fixpoint subst (z : atom) (u : exp) (e : exp) : exp :=
  match e with
    | exp_bvar i => e
    | exp_fvar x => if x == z then u else e
    | exp_num _ => e
    | exp_str _ => e
    | exp_let e1 e2 => exp_let (subst z u e1) (subst z u e2)
    | exp_op o e1 e2 => exp_op o (subst z u e1) (subst z u e2)
  end.

(** The [Fixpoint] keyword defines a Coq function.  As all functions
    in Coq must be total.  The annotation [{struct e}] indicates the
    termination metric---all recursive calls in this definition are
    made to arguments that are structurally smaller than [e].
    Note also that subst uses the notation [x == z] for decidable atom
    equality.  This notation is defined in the Metatheory library.
    We define a notation for free variable substitution that mimics
    standard mathematical notation.
*)

Notation "[ z ~> u ] e" := (subst z u e) (at level 68).


(** To demonstrate how free variable substitution works, we need to
    reason about atom equality.
*)

Parameter Z : atom.
Check (Y == Z).

(** The decidable atom equality function returns a sum. If the two
    atoms are equal, the left branch of the sum is returned, carrying
    a proof of the proposition that the atoms are equal.  If they are
    not equal, the right branch includes a proof of the disequality.
    The demo below uses three new tactics:
    - The tactic [simpl] reduces a Coq expression to its normal
      form.
    - The tactic [destruct (Y==Y)] considers the two possible
      results of the equality test.
    - The tactic [Case] marks cases in the proof script.
      It takes any string as its argument, and puts that string in
      the hypothesis list until the case is finished.
*)

Lemma demo_subst1:
  [Y ~> exp_fvar Z] (exp_let (exp_num 1) (exp_op plus (exp_bvar 0) (exp_fvar Y)))
                  = (exp_let (exp_num 1) (exp_op plus (exp_bvar 0) (exp_fvar Z))).
Proof.
  simpl.
  destruct (Y==Y).
  -  auto.
  -  destruct n. auto.
Qed.

(** *** Exercise [subst_eq_var]
    We can use almost the same proof script as above to state how substitution
    works in the variable case. Try it on your own.  *)

Lemma subst_eq_var: forall (x : atom) u,
  [x ~> u](exp_fvar x) = u.
Proof.
  intros x u. 
  simpl.
  destruct (x==x).
    - reflexivity.
    - destruct n. reflexivity.
Qed. 

Lemma subst_neq_var : forall (x y : atom) u,
  y <> x -> [x ~> u](exp_fvar y) = exp_fvar y.
Proof.
  intros x y u ynx. 
  simpl.
  destruct (y==x).
   - contradiction.
   - reflexivity.
Qed. 


(*************************************************************************)
(** * Free variables *)
(*************************************************************************)

(** The function [fv], defined below, calculates the set of free
    variables in an expression.  Because we are using a locally
    nameless representation, where bound variables are represented as
    indices, any name we see is a free variable of a term.
*)

Fixpoint fv (e : exp) {struct e} : atoms :=
  match e with
    | exp_fvar x => singleton x
    | exp_let e1 e2 => fv e1 `union` fv e2
    | exp_op o e1 e2 => fv e1 `union` fv e2
    | _ => empty 
  end.

(** The type [atoms] represents a finite set of elements of type
    [atom].  The notation for infix union is defined in the Metatheory
    library.
*)

(* Demo [f_equal]
  The tactic [f_equal] converts a goal of the form [f e1 = f e1'] in
  to one of the form [e1 = e1'], and similarly for [f e1 e2 = f e1'
  e2'], etc.
*)
Lemma f_equal_demo : forall e1 e2, e1 = e2 -> fv e1 = fv e2.
Proof.
  intros e1 e2 EQ.
  f_equal.
  assumption.
Qed.

(* Demo [fsetdec]
   The tactic [fsetdec] solves a certain class of propositions
   involving finite sets. See the documentation in [FSetWeakDecide]
   for a full specification.
*)

Lemma fsetdec_demo : forall (x :atom) (S : atoms),
  x `in` (singleton x `union` S).
Proof.
  fsetdec.
Qed.


(** Demo [subst_fresh]
    To show the ease of reasoning with these definitions, we will prove a
    standard result from lambda calculus: if a variable does not
    appear free in a term, then substituting for it has no effect.
    HINTS: Prove this lemma by induction on [e].
    - You will need to use [simpl] in many cases.  You can [simpl]
      everything everywhere (including hypotheses) with the
      pattern [simpl in *].
    - Part of this proof includes a false assumption about free
      variables.  Destructing this hypothesis produces a goal about
      finite set membership that is solvable by [fsetdec].
*)

Lemma subst_fresh : forall (x : atom) e u,
  x `notin` fv e -> [x ~> u] e = e.
Proof.
  intros x e u xnfe. induction e as [| fvar | | |op ex1 IHe1 ex2 IHe2| l1 IHe1 l2 IHe2]. 
     - simpl. reflexivity.
     - simpl. destruct (fvar==x).
        + destruct xnfe. simpl. fsetdec.
        + reflexivity.
     - simpl. reflexivity.
     - simpl. reflexivity.
     - simpl. simpl in *. destruct_notin. rewrite -> (IHe1 xnfe). rewrite -> (IHe2 NotInTac). reflexivity. 
     - simpl. simpl in *. destruct_notin. rewrite -> (IHe1 xnfe). rewrite -> (IHe2 NotInTac). reflexivity.
Qed.

(* Take-home Demo: Prove that free variables are not introduced by
   substitution.
   This proof actually is very automatable ([simpl in *; auto.] takes
   care of all but the fvar case), but the explicit proof below
   demonstrates two parts of the finite set library. These two parts
   are the tactic [destruct_notin] and the lemma [notin_union], both
   defined in the module [FSetWeakNotin].
   Before stepping through this proof, you should go to that module
   to read about those definitions and see what other finite set
   reasoning is available.
  *)
Lemma subst_notin_fv : forall x y u e,
   x `notin` fv e -> x `notin` fv u ->
   x `notin` fv ([y ~> u]e).
Proof.
  intros x y u e Fr1 Fr2.
  induction e; simpl in *.
  - assumption.
  - destruct (a == y).
    + assumption.
    + simpl. assumption.
  - assumption.
  - assumption.
  - destruct_notin.
    apply notin_union.  apply IHe1. assumption. apply IHe2. assumption.
  - destruct_notin.
    apply notin_union.  apply IHe1. assumption. apply IHe2. assumption.
Qed.

Lemma subst_notin : forall x u e, x `notin` fv u -> x `notin` fv ([x ~> u] e).
Proof. intros x u e xnu. induction e.
       - simpl. fsetdec.
       - simpl. destruct (a == x).
          + apply xnu.
          + simpl. fsetdec.
       - simpl. fsetdec.
       - simpl. fsetdec. 
       - simpl. fsetdec.
       - simpl. fsetdec.
Qed.  
       

(*************************************************************************)
(** * Opening *)
(*************************************************************************)

(** Opening replaces an index with a term.  It corresponds to informal
    substitution for a bound variable, such as in a rule for beta
    reduction.  Note that only "dangling" indices (those that do not
    refer to any abstraction) can be opened.  Opening has no effect
    for terms that are locally closed.
    Natural numbers are just an inductive datatype with two
    constructors: [O] (as in the letter 'oh', not 'zero') and [S],
    defined in Coq.Init.Datatypes.  Coq allows literal natural numbers
    to be written using standard decimal notation, e.g., 0, 1, 2, etc.
    The notation [k == i] is the decidable equality function for
    natural numbers (cf. [Coq.Peano_dec.eq_nat_dec]).  This notation
    is defined in the Metatheory library.
    We make several simplifying assumptions in defining [open_rec].
    First, we assume that the argument [u] is locally closed.  This
    assumption simplifies the implementation since we do not need to
    shift indices in [u] when passing under a binder.  Second, we
    assume that this function is initially called with index zero and
    that zero is the only unbound index in the term.  This eliminates
    the need to possibly subtract one in the case of indices.
    There is no need to worry about variable capture because bound
    variables are indices.
*)

Fixpoint open_rec (k : nat) (u : exp)(e : exp)
  {struct e} : exp :=
  match e with
    | exp_bvar i => if k == i then u else (exp_bvar i)
    | exp_let e1 e2 => exp_let (open_rec k u e1) (open_rec (S k) u e2)
    | exp_op o e1 e2 => exp_op o (open_rec k u e1) (open_rec k u e2)
    | _ => e 
  end.

(** Many common applications of opening replace index zero with an
    expression or variable.  The following definition provides a
    convenient shorthand for such uses.  Note that the order of
    arguments is switched relative to the definition above.  For
    example, [(open e x)] can be read as "substitute the variable [x]
    for index [0] in [e]" and "open [e] with the variable [x]."
    Recall that the coercions above let us write [x] in place of
    [(exp_fvar x)].
*)

Definition open e u := open_rec 0 u e.

(** This next demo shows the operation of [open] on the term 
      "let x be "a" in __ + x"  where we replace the __ with Y.
*)

Lemma demo_open :
  open (exp_let (exp_str "a") (exp_op plus (exp_bvar 1) (exp_bvar 0))) (exp_fvar Y) =
       (exp_let (exp_str "a") (exp_op plus (exp_fvar Y) (exp_bvar 0))).
Proof. unfold open. simpl. reflexivity.
Qed.

(* HINT for demo: To show the equality of the two sides below, use the
   tactics [unfold], which replaces a definition with its RHS and
   reduces it to head form, and [simpl], which reduces the term the
   rest of the way.  Then finish up with [auto].  *)


(*************************************************************************)
(*                                                                       *)
(*  Stretch break (5 mins)                                               *)
(*                                                                       *)
(*************************************************************************)


(*************************************************************************)
(** * Local closure *)
(*************************************************************************)

(** Recall that [exp] admits terms that contain unbound indices.  We
    say that a term is locally closed when no indices appearing in it
    are unbound.  The proposition [lc_e e] holds when an expression [e]
    is locally closed.
*)

Inductive lc_e : exp -> Prop :=
  | lc_e_var : forall (x:atom),
      lc_e (exp_fvar x)
  | lc_e_num : forall n, lc_e (exp_num n)
  | lc_e_str : forall s, lc_e (exp_str s)
  | lc_e_let : forall e1 e2,
      lc_e e1 -> (forall x, x `notin` fv e2 -> lc_e (open e2 (exp_fvar x))) ->
      lc_e (exp_let e1 e2)
  | lc_e_app : forall e1 e2 op,
      lc_e e1 -> lc_e e2 ->
      lc_e (exp_op op e1 e2).

Hint Constructors lc_e.

(* The primary use of the local closure proposition is to support induction on
    the syntax of abstract binding trees, such as discussed in Chapter 1.2 of
    PFPL.  The induction principle for type [exp] won't do: it requires
    reasoning about terms with dangling indices. The local closure predicate
    ensures that each case of an inductive proof need only reason about
    locally closed terms by replacing all bound variables with free variables
    in its definition.
    Further, when we do induction on the abstract syntax of expressions with
    binding we need to be sure that we have a strong enough induction
    principle, similar to the "structural induction modulo fresh renaming"
    in PFPL.  
    Unfortunately, the lc_e definition above doesn't stack up. 
 *)

Check lc_e.

(*************************************************************************)
(** Cofinite quantification *)
(*************************************************************************)

(* In the next example, we will reexamine the definition of
   local closure in the [let] case.
   The lemma [subst_lc] says that local closure is preserved by
   substitution.  Let's start working through this proof.
*)

Lemma subst_lc_0 : forall (x : atom) u e,
  lc_e e ->
  lc_e u ->
  lc_e ([x ~> u] e).
Proof.
  intros x u e He Hu.
  induction He.
  - simpl.
    destruct (x0 == x).
      auto.
      auto.
  - simpl. auto.
  - simpl. auto.
  - simpl.
    Print lc_e_let. 
    apply lc_e_let. apply IHHe. 
    intros x0 xne2.  
Admitted.

(** Here we are stuck. We don't know that [x0] is not in the free
    variables of [u].
    The solution is to change the *definition* of local closure so
    that we get a different induction principle.  Currently, in the
    [lc_abs] case, we show that an abstraction is locally closed by
    showing that the body is locally closed after it has been opened
    with one particular variable.
<<
  | lc_let : forall (x : atom) e1 e2,
      lc_e e1 ->
      x `notin` fv e2 ->
      lc_e (open e2 x) ->
      lc_e (exp_let e1 e2)
>>
    Therefore, our induction hypothesis in this case only applies to
    that variable. From the hypothesis list in the [lc_let] case:
      x0 : atom,
      IHHe2 : lc_e ([x ~> u]open e2 x0)
    The problem is that we don't have any assumptions about [x0]. It
    could very well be equal to [x].
    A stronger induction principle provides an IH that applies to many
    variables. In that case, we could pick one that is "fresh enough".
    To do so, we need to revise the above definition of lc and replace
    the type of lc_let with this one:
<<
  | lc_let : forall L e1 e2,
      lc e1 ->
      (forall x, x `notin` L -> lc (open e2 x)) ->
      lc (exp_let e1 e2)
>>
   This rule says that to show that an abstraction is locally closed,
   we need to show that the body is closed, after it has been opened by
   any atom [x], *except* those in some set [L]. With this rule, the IH
   in this proof is now:
     H0 : forall x0 : atom, x0 `notin` L -> lc ([x ~> u]open e2 x0)
   Below, lc is the local closure judgment revised to use this new
   rule in the abs case. We call this "cofinite quantification"
   because the IH applies to an infinite number of atoms [x0], except
   those in some finite set [L].
   Changing the rule in this way does not change what terms are locally
   closed.  (For more details about cofinite-quantification see:
   "Engineering Formal Metatheory", Aydemir, Chargu'eraud, Pierce,
   Pollack, Weirich. POPL 2008.)
*)

Inductive lc : exp -> Prop :=
  | lc_var : forall (x:atom), lc (exp_fvar x)
  | lc_num : forall n : nat, lc (exp_num n)
  | lc_str : forall s : string, lc (exp_str s)
  | lc_let : forall L (e1 e2 : exp),
      lc e1 
      -> (forall x, x `notin` L -> lc (open e2 (exp_fvar x)))
      -> lc (exp_let e1 e2)
  | lc_op : forall (e1 e2 : exp) (op : op),
      lc e1
      -> lc e2
      -> lc (exp_op op e1 e2).
                                                           
Hint Constructors lc.


(* Demo [subst_lc]:
   Once we have changed the definition of lc, we can complete the
   proof of subst_lc.
    HINT: apply lc_let with cofinite set (L `union` singleton x).
    This gives us an atom x0, and a hypothesis that
    x0 is fresh for both L and x.
*)

Lemma notins : forall x l l', x `notin` (l `union` l') -> x `notin` l'.
Proof. fsetdec.
Qed.

Inductive bot : Type.

Lemma neq : forall x x', x `notin` singleton x' -> x <> x'.
Proof. fsetdec.
Qed.

Lemma subst_lc : forall (x : atom) u e,
  lc e ->
  lc u ->
  lc ([x ~> u] e).
Proof.
  intros x u e He Hu.
  induction He. 
  - simpl.
   destruct (x0 == x).
     auto.
     auto.
  - simpl. auto.
  - simpl. auto.
  - simpl. apply lc_let with (L `union` singleton x). 
     apply IHHe.
     intros x0 x0nl. destruct (x0 == x).
       + apply notins in x0nl. apply neq in x0nl. contradiction.
       +  
     
    (* FILL IN HERE (and delete "Admitted") *) Admitted.


Check lc_ind.

(* Going deeper:
   Compare the induction principle with that of PFPL (specialized to the abt for E). 
   An Abstract Binding Tree, such as E, is parameterized by X, a set of free variables that 
   can appear in an abt.  For example, 
       the (free) variable x is a member of E [ {{x}} ] and 
       x + y is a member of E [ {{ x }} \u {{ y }} ].
       
   For a given term, indexed by a given set of free variables, the induction 
   principle reads:
   To show a property  P : forall X, E[X] -> Prop holds for an arbitrary 
   expression e in E[X] it suffices to show:
        forall x, x `in` X -> P x
        forall n, P n
        forall s, P s
        forall x x' e1 e2, such that x' notin X, 
           P e1 -> P ( [ x' / x ] e2 ) -> P (let x be e1 in e2)
        forall e1 e2, P e1 -> P e2 -> P (e1 `op` e2)
   In other words, in the variable case, we need to show the property for 
   all variables that actually appear in the term (though often in the proof, this 
   set will be abstract). Also in the let case, we need to show the property hold 
   for an arbitrary x' that does *not* appear in X. When we do the proof, 
   we get to pick any X, as long as it is larger than the fv of e. In practice, this 
   induction principle behaves like co-finite quantification. 
  
*) 


(*************************************************************************)
(** Properties about basic operations *)
(*************************************************************************)

(** We also define a notation for [open_rec] to make stating some of
    the properties simpler. However, we don't need to use open_rec
    outside of this part of the tutorial so we make it a local
    notation, confined to this section. *)

Section BasicOperations.
Local Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).

(** The first property we would like to show is the analogue to
    [subst_fresh]: index substitution has no effect for closed terms.
    Here is an initial attempt at the proof.
*)

Lemma open_rec_lc_0 : forall k u e,
  lc e ->
  e = {k ~> u} e.
Proof.
  intros k u e LC.
  induction LC.
  -  simpl.
    auto.
  -  simpl.
    f_equal.
Admitted.

(** At this point there are two problems.  Our goal is about
    substitution for index [S k] in term [e], while our induction
    hypothesis IHLC only tells use about index [k] in term [open e x].
    To solve the first problem, we generalize our IH over all [k].
    That way, when [k] is incremented in the [abs] case, it will still
    apply.  Below, we use the tactic [generalize dependent] to
    generalize over [k] before using induction.
*)

Lemma open_rec_lc_1 : forall k u e,
  lc e ->
  e = {k ~> u} e.
Proof.
  intros k u e LC.
  generalize dependent k.
  induction LC.
  - simpl. auto.
  - simpl. auto.
  - simpl. auto.
  - simpl.
    intro k.
    f_equal. auto.
Admitted.

(** At this point we are still stuck because the IH concerns
    [open e2 x] instead of [e2]. The result that we need is that if an
    index substitution has no effect for an opened term, then it has
    no effect for the raw term (as long as we are *not* substituting
    for [0], hence [S k] below).
<<
   open e x = {S k ~> u}(open e x)  -> e = {S k ~> u} e
>>
   In other words, expanding the definition of open:
<<
   {0 ~> x}e = {S k ~> u}({0 ~> x} e)  -> e = {S k ~> u} e
>>
   Of course, to prove this result, we must generalize
   [0] and [S k] to be any pair of inequal numbers to get a strong
   enough induction hypothesis for the [abs] case.
 *)

Lemma open_rec_lc_core : forall e j v i u,
  i <> j ->
  {j ~> v} e = {i ~> u} ({j ~> v} e) ->
  e = {i ~> u} e.
Proof.
  induction e; intros j v i u Neq H; simpl in *.
  - Case "exp_bvar".
    destruct (j == n);  destruct (i == n).
      SCase "j = n = i".
        subst n. destruct Neq. auto.
      SCase "j = n, i <> n".
        auto.
      SCase "j <> n, i = n".
        subst n. simpl in H.
        destruct (i == i).
           SSCase "i=i".
             auto.
           SSCase "i<>i".
             destruct n. auto.
      SCase "j <> n, i <> n".
        auto.
 - Case "exp_fvar". auto.
 - Case "exp_num". auto.
 - Case "exp_str". auto.
 - Case "exp_op".
    inversion H.
    f_equal.
    eapply IHe1; eauto.
    eapply IHe2; eauto.
 - Case "exp_let".
    inversion H.
    f_equal.
    eapply IHe1; eauto.
    apply  IHe2 with (j := S j) (u := u) (i := S i) (v := v).
    auto.
    auto.
Qed.

(** Challenge Exercise [proof refactoring]
   
   We've proven the above lemma very explicitly, so that you can step through
   it slowly to see how it works. However, with automation, it is possible to
   give a *much* shorter proof. Reprove this lemma on your own to see how
   compact you can make it.  *)

(** With the help of this lemma, we can complete the proof. *)

Lemma open_rec_lc : forall k u e,
  lc e -> e = {k ~> u} e.
Proof.
  intros k u e LC.
  generalize dependent k.
  induction LC.
  - simpl.
    auto.
  - simpl. auto.   
  - simpl. auto.
  - simpl.
    intro k.
    f_equal.
    auto.
    unfold open in *.
    pick fresh x for L. (* tactic to choose a fresh x *)
    apply open_rec_lc_core with
      (i := S k) (j := 0) (u := u) (v := exp_fvar x).
    auto.
    auto.
  - intro k.
    simpl.
    f_equal.
    auto.
    auto.
Qed.

(* Below are two more important properties of open and subst. *)

(** *** Exercise [subst_open_rec] *)

(** The next lemma demonstrates that free variable substitution
    distributes over index substitution.
    The proof of this lemma is by straightforward induction over
    [e1]. When [e1] is a free variable, we need to appeal to
    [open_rec_lc], proved above.
*)

Lemma subst_open_rec : forall e1 e2 u (x : atom) k,
  lc u ->
  [x ~> u] ({k ~> e2} e1) = {k ~> [x ~> u] e2} ([x ~> u] e1).
Proof.
  (* EXERCISE *) Admitted.


(** *** Exercise [subst_open] *)

(** The lemma above is most often used with [k = 0] and
    [e2] as some fresh variable. Therefore, it simplifies matters
    to define the following useful corollary.
    HINT: Do not use induction.
    Rewrite with [subst_open_rec] and [subst_neq_var].
*)

Lemma subst_open : forall (x : atom) u e1 e2,
  lc u ->
  open ([x ~> u] e1) e2 = [x ~> u] (open e1 e2).
Proof.
  (* EXERCISE *) Admitted.

(** *** Exercise [subst_intro] *)

(** This lemma states that opening can be replaced with variable
    opening and substitution.
    HINT: Prove by induction on [e], first generalizing the
    argument to [open_rec] by using the [generalize] tactic, e.g.,
    [generalize 0].
*)

Lemma subst_intro : forall (x : atom) u e,
  x `notin` (fv e) ->
  open e u = [x ~> u](open e (exp_fvar x)).
Proof.
  (* EXERCISE *) Admitted.

(** Challenge Exercise [fv_open]
    We must show how open interacts with all functions defined over
    expressions. We just saw an instance with substitution --- but we must
    also say something about 'fv'.
    Below, try to prove a similar property about the interaction between fv
    and open. Note that we don't know for sure that the bound variable
    actually appears in the term e1, so we get a subset, not an equivalence.
    This exercise is challenging (more so than some of the other challenges
    below), and fsetdec won't be able to help you right off the bat. You'll
    need to generalize the induction hypothesis, break the problem down a bit
    first and give fsetdec some extra information.
    HINTS: Generalize the induction hypothsis Do some forward reasoning with
       the "pose" tactic.  Check AtomSetProperties.union_subset_3.
*)

Lemma fv_open : forall e1 e2,
    fv (open e1 e2) [<=] fv e2 \u fv e1.
Proof.
   (* CHALLENGE EXERCISE *) Admitted.
    
End BasicOperations.


    
(*************************************************************************)
(*                                                                       *)
(*  Break                                                                *)
(*                                                                       *)
(*************************************************************************)


(*************************************************************************)
(** * Typing environments *)
(*************************************************************************)

(** We represent environments as association lists (lists of pairs of
    keys and values) whose keys are [atom]s.
*)


Notation env := (list (atom * typ)).

(** Environments bind [atom]s to [typ]s.  We define an abbreviation [env] for
    the type of these environments.  Coq will print [list (atom * typ)] as
    [env], and we can use [env] as a shorthand for writing [list (atom *
    typ)].  Lists are defined in Coq's standard library, with the constructors
    [nil] and [cons].  The list library includes the [::] notation for cons as
    well as standard list operations such as append, map, and fold. The infix
    operation "++" is list append.  The Metatheory library extends this
    reasoning by instantiating the AssocList library to provide support for
    association lists whose keys are [atom]s.  Everything in this library is
    polymorphic over the type of objects bound in the environment.  Look in
    AssocList for additional details about the functions and predicates that
    we mention below.  *)

(** Environment equality *)

(** When reasoning about environments, we often need to talk about
    bindings in the "middle" of an environment. Therefore, it is common
    for lemmas and definitions to use list append in their statements.
    Unfortunately, list append is associative, so two Coq expressions may
    denote the same environment even though they are not equal.
    The tactic [simpl_env] reassociates all concatenations of
    environments to the right.
*)

Lemma append_assoc_demo : forall (E0 E1 E2 E3:env),
  E0 ++ (E1 ++ E2) ++ E3 = E0 ++ E1 ++ E2 ++ E3.
Proof.
  intros.
  auto. (* Does nothing. *)
  simpl_env.
  reflexivity.
Qed.

(** To make environments easy to read, instead of building them from
    [nil] and [cons], we prefer to build them from the following
    components:
      - [nil]: The empty list.
      - [one]: Lists consisting of exactly one item.
      - [++]:  List append.
   Furthermore, we introduce compact notation for one (singleton lists):
   [(x ~ T)] is the same as [one (x, T)].
*)

(** The simpl_env tactic actually puts lists built from only nil, one
    and [++] into a "normal form". This process reassociates all appends
    to the right, removes extraneous nils converts cons to singleton
    lists with an append.
*)

Lemma simpl_env_demo : forall (x y:atom) (T1 T2:typ) (E F:env),
   ((x ~ T1) ++ nil) ++ (y,T2) :: (nil ++ E) ++ F =
   (x ~ T1) ++ (y ~ T2) ++ E ++ F.
Proof.
   intros.
   (* simpl_env puts the left side into the normal form. *)
   simpl_env.
   reflexivity.
Qed.

(** Note that the [simpl] tactic doesn't produce the "normal form" for
    environments. It should always be followed up with [simpl_env].
    Furthermore, to convert an environment to any equivalent form
    other than the normal form (perhaps to apply a lemma) use the
    tactic [rewrite_env].
*)

Lemma rewrite_env_demo : forall (x y:atom) (T:typ) P,
  (forall E, P ((x,T):: E) -> True) ->
  P (x ~ T) ->
  True.
Proof.
  intros x y T P H.
  (* apply H. fails here. *)
  rewrite_env ((x,T) :: nil).
  apply H.
Qed.

(** Environment operations. *)

(** The ternary predicate [binds] holds when a given binding is
    present somewhere in an environment.
*)

Lemma binds_demo : forall (x:atom) (T:typ) (E F:env),
  binds x T (E ++ (x ~ T) ++ F).
Proof.
  auto.
Qed.

(** The function [dom] computes the domain of an environment,
    returning a finite set of [atom]s. Note that we cannot use Coq's
    equality for finite sets, we must instead use a defined relation
    [=] for atom set equality.
 *)

Lemma dom_demo : forall (x y : atom) (T : typ),
  dom (x ~ T) [=] singleton x.
Proof.
  auto.
Qed.

(** The unary predicate [uniq] holds when each atom is bound at most
    once in an environment.
*)

Lemma uniq_demo : forall (x y : atom) (T : typ),
  x <> y -> uniq ((x ~ T) ++ (y ~ T)).
Proof.
  auto.
Qed.

(*************************************************************************)
(** * Tactic support for freshness *)
(*************************************************************************)

(** When picking a fresh atom or applying a rule that uses cofinite
    quantification, choosing a set of atoms to be fresh for can be
    tedious.  In practice, it is simpler to use a tactic to choose the
    set to be as large as possible.
    The tactic [gather_atoms] is used to collect together all the
    atoms in the context.  It relies on an auxiliary tactic,
    [gather_atoms_with] (from MetatheoryAtom), which maps a function
    that returns a finite set of atoms over all hypotheses with the
    appropriate type.
*)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (atom * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv x) in
  constr:(A `union` B `union` C `union` D).

(** A number of other, useful tactics are defined by the Metatheory
    library, and each depends on [gather_atoms].  By redefining
    [gather_atoms], denoted by the [::=] in its definition below, we
    automatically update these tactics so that they use the proper
    notion of "all atoms in the context."
    For example, the tactic [(pick fresh x)] chooses an atom fresh for
    "everything" in the context.  It is the same as [(pick fresh x for
    L)], except where [L] has been computed by [gather_atoms].
    The tactic [(pick fresh x and apply H)] applies a rule [H] that is
    defined using cofinite quantification.  It automatically
    instantiates the finite set of atoms to exclude using
    [gather_atoms].
*)


(** *** Example
    Below, we reprove [subst_lc] using [(pick fresh and apply)].
    Step through the proof below to see how [(pick fresh and apply)]
    works.
*)

Lemma subst_lc_alternate_proof : forall (x : atom) u e,
  lc e ->
  lc u ->
  lc ([x ~> u] e).
Proof.
  intros x u e He Hu.
  induction He; simpl; auto.
  - destruct (x0 == x).
     auto.
     auto.
  - pick fresh y and apply lc_let.
    auto.
    (* Here, take note of the hypothesis [Fr]. *)
    rewrite subst_open. auto. auto. 
Qed.

(** Challenge Exercise [subst_lc_inverse]
    Try it yourself, for the following
    "inverse" to subst_lc theorem.
    Hint: do this proof by induction on the local closure judgement.  You'll
    need to generalize the theorem statement to get it in the right
    form. You'll also need to [destruct] e in each case to see what it could
    have been before the substitution.  
*)

Lemma subst_lc_inverse : forall x u e, lc ([x ~> u] e) -> lc u -> lc e.
Proof.
(* CHALLENGE EXERCISE *) Admitted.



(*************************************************************************)
(** * Typing relation (Section 4.2) *)
(*************************************************************************)

(** The definition of the typing relation is straightforward.  In
    order to ensure that the relation holds for only well-formed
    environments, we check in the [typing_var] case that the
    environment is [uniq].  The structure of typing derivations
    implicitly ensures that the relation holds only for locally closed
    expressions.  Finally, note the use of cofinite quantification in
    the [typing_let] case.
*)

Inductive typing : env -> exp -> typ -> Prop :=
| typing_var : forall E (x : atom) T,
    uniq E ->
    binds x T E ->
    typing E (exp_fvar x) T
| typing_str  : forall s E,
    uniq E ->
    typing E (exp_str s) typ_string
| typing_num  : forall i E,
    uniq E ->
    typing E (exp_num i) typ_num
| typing_let : forall (L : atoms) E e1 e2 T1 T2,
    typing E e1 T1 ->
    (forall (x:atom), x `notin` L ->
                 typing ((x ~ T1) ++ E) (open e2 (exp_fvar x)) T2) ->
    typing E (exp_let e1 e2) T2
| typing_op : forall E e1 e2,
    typing E e1 typ_num ->
    typing E e2 typ_num ->
    typing E (exp_op plus e1 e2) typ_num.

(* NOTE: no typing rules for times or cat. EXERCISE: You add them and 
   extend all proofs! *)

(** We add the constructors of the typing relation as hints to be used
    by the [auto] and [eauto] tactics.
*)
Hint Constructors typing.


(* Note that the typing relation *only* includes locally closed terms. *)

Lemma typing_lc : forall G e T, typing G e T -> lc e.
Proof. 
  intros. induction H; eauto.
Qed.


(*************************************************************************)
(** * Unicity of Typing *)
(*************************************************************************)

(** *** Exercise [unicity]
   As PFPL Lemma 4.1 shows, there is only one type for each given term. We can
   state that property in Coq using the following lemma.  The key part of this
   proof is the lemma [binds_unique] from the metatheory library.  This lemma
   states that there is only one type for a particular variable in the
   context. 
 *)

Check binds_unique.

Lemma unicity : forall G e t1, typing G e t1 -> forall t2, typing G e t2 -> t1 = t2.
(* EXERCISE *) Admitted.


(*************************************************************************)
(** * Weakening (Lemma 4.3) *)
(*************************************************************************)

(** Weakening states that if an expression is typeable in some
    environment, then it is typeable in any well-formed extension of
    that environment.  This property is needed to prove the
    substitution lemma.
    As stated below (and in PFPL), this lemma is not directly proveable.  The
    natural way to try proving this lemma proceeds by induction on the
    typing derivation for [e].
*)

Lemma typing_weakening_0 : forall E F e T,
  typing E e T ->
  uniq (F ++ E) ->
  typing (F ++ E) e T.
Proof.
  intros E F e T H J.
  induction H; eauto.
  - Case "typing_let".
    pick fresh x and apply typing_let.
    eauto.
    (* ... stuck here ... *)
Admitted.

(** We are stuck in the [typing_let] case because the induction
    hypothesis [H0] applies only when we weaken the environment at its
    head.  In this case, however, we need to weaken the environment in
    the middle; compare the conclusion at the point where we're stuck
    to the hypothesis [H], which comes from the given typing derivation.
    We can obtain a more useful induction hypothesis by changing the
    statement to insert new bindings into the middle of the
    environment, instead of at the head.  However, the proof still
    gets stuck, as can be seen by examining each of the cases in
    the proof below.
    Note: To view subgoal n in a proof, use the command "[Show n]".
    To work on subgoal n instead of the first one, use the command
    "[Focus n]".
*)

Lemma typing_weakening_strengthened_0 : forall (E F G : env) e T,
  typing (G ++ E) e T ->
  uniq (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
Proof.
  intros E F G e T H J.
  induction H.
  Case "typing_var".
    (* The E0 looks strange in the [typing_var] case. *)
  Focus 4.
  Case "typing_let".
    (* The [typing_let] case still does not have a strong enough IH. *)
Admitted.

(** The hypotheses in the [typing_var] case include an environment
    [E0] that that has no relation to what we need to prove.  The
    missing fact we need is that [E0 = (G ++ E)].
    The problem here arises from the fact that Coq's [induction]
    tactic let's us only prove something about all typing derivations.
    While it's clear to us that weakening applies to all typing
    derivations, it's not clear to Coq, because the environment is
    written using concatenation.  The [induction] tactic expects that
    all arguments to a judgement are variables.  So we see [E0] in the
    proof instead of [(G ++ E)].
    The solution is to restate the lemma.  For example, we can prove
<<
  forall E F E' e T, typing E' e T ->
  forall G, E' = G ++ E -> uniq (G ++ F ++ E) -> typing (G ++ F ++ E) e T.
>>
    The equality gets around the problem with Coq's [induction]
    tactic.  The placement of the [(forall G)] quantifier gives us a
    sufficiently strong induction hypothesis in the [typing_let] case.
    However, we prefer not to state the lemma in the way shown above,
    since it is not as readable as the original statement.  Instead,
    we use a tactic to introduce the equality within the proof itself.
    The tactic [(remember t as t')] replaces an object [t] with the
    identifier [t'] everywhere in the goal and introduces an equality
    [t' = t] into the context.  It is often combined with [generalize
    dependent], as illustrated below.
*)


(** *** Exercise [typing_weakening_strengthened] 
    See how we use [remember as] in the proof below for weakening.
    Then, complete the proof below.
    HINTS:
       - The [typing_var] case follows from [binds_weaken], the
         weakening lemma for the [binds] relation.
       - The [typing_let] case follows from the induction
         hypothesis, but the [apply] tactic may be unable to unify
         things as you might expect.
           -- Recall the [pick fresh and apply] tactic.
           -- In order to apply the induction hypothesis, use
              [rewrite_env] to reassociate the list operations.
           -- After applying the induction hypothesis, use
              [simpl_env] to use [uniq_push].
           -- Here, use [auto] to solve facts about finite sets of
              atoms, since it will simplify the [dom] function behind
              the scenes.  [fsetdec] does not work with the [dom]
              function.
       - The [typing_op] case follows directly from the induction
         hypotheses.
  *)

Lemma typing_weakening_strengthened :  forall (E F G : env) e T,
  typing (G ++ E) e T ->
  uniq (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
Proof.
  intros E F G e T H.
  remember (G ++ E) as E'.
  generalize dependent G.
  induction H; intros G Eq Uniq; subst.
 (* EXERCISE *) Admitted.


(** *** Example
    We can now prove our original statement of weakening.  The only
    interesting step is the use of the rewrite_env tactic.
*)

Lemma typing_weakening : forall (E F : env) e T,
    typing E e T ->
    uniq (F ++ E) ->
    typing (F ++ E) e T.
Proof.
  intros E F e T H J.
  rewrite_env (nil ++ F ++ E).
  apply typing_weakening_strengthened; auto.
Qed.

(** 
    
    NOTE: If we view typing contexts as ordered lists of typing assumptions, then
    the type system shown in section 4.2 of PFPL does NOT satisfy the 
    weakening property.  Why not? 
*)

(*************************************************************************)
(** * Substitution *)
(*************************************************************************)

(** Having proved weakening, we can now prove the usual substitution
    lemma, which we state both in the form we need and in the
    strengthened form needed to make the proof go through.
<<
  typing_subst_simple : forall E e u S T z,
    typing ((z ~ S) ++ E) e T ->
    typing E u S ->
    typing E ([z ~> u] e) T
  typing_subst : forall E F e u S T z,
    typing (F ++ (z ~ S) ++ E) e T ->
    typing E u S ->
    typing (F ++ E) ([z ~> u] e) T
>>
    The proof of the strengthened statement proceeds by induction on
    the given typing derivation for [e].  The most involved case is
    the one for variables; the others follow from the induction
    hypotheses.
*)


(** *** Exercise [typing_subst_var_case]
    Below, we state what needs to be proved in the [typing_var] case
    of the substitution lemma.  Fill in the proof.
    Proof sketch: The proof proceeds by a case analysis on [(x == z)],
    i.e., whether the two variables are the same or not.
      - If [(x = z)], then we need to show [(typing (F ++ E) u T)].
        This follows from the given typing derivation for [u] by
        weakening and the fact that [T] must equal [S].
      - If [(x <> z)], then we need to show [(typing (F ++ E) x T)].
        This follows by the typing rule for variables.
    HINTS: Lemmas [binds_mid_eq], [uniq_remove_mid],
    and [binds_remove_mid] are useful.
  *)

Lemma typing_subst_var_case : forall (E F : env) u S T (z x : atom),
  binds x T (F ++ (z ~ S) ++ E) ->
  uniq (F ++ (z ~ S) ++ E) ->
  typing E u S ->
  typing (F ++ E) ([z ~> u] (exp_fvar x)) T.
Proof.
  intros E F u S T z x H J K.
  simpl.
 (* EXERCISE *) Admitted.

(** *** Note
    The other two cases of the proof of the substitution lemma are
    relatively straightforward.  However, the case for [typing_let]
    needs the fact that the typing relation holds only for
    locally-closed expressions.
*)

(** *** Exercise [typing_subst]
    Complete the proof of the substitution lemma. The proof proceeds
    by induction on the typing derivation for [e].  The initial steps
    should use [remember as] and [generalize dependent] in a manner
    similar to the proof of weakening.
   HINTS:
      - Use the lemma proved above for the [typing_var] case.
      - The [typing_let] case follows from the induction hypothesis.
         -- Use [simpl] to simplify the substitution.
          -- Recall the tactic [pick fresh and apply].
          -- In order to use the induction hypothesis, use
             [subst_open] to push the substitution under the
             opening operation.
          -- Recall the lemma [typing_to_lc] and the
             [rewrite_env] and [simpl_env] tactics.
      - The [typing_op] case follows from the induction hypotheses.
        Use [simpl] to simplify the substitution.
*)

Lemma typing_subst : forall (E F : env) e u S T (z : atom),
  typing (F ++ (z ~ S) ++ E) e T ->
  typing E u S ->
  typing (F ++ E) ([z ~> u] e) T.
Proof.
(* EXERCISE *) Admitted.


(** *** Exercise [typing_subst_simple]
    Complete the proof of the substitution lemma stated in the form we
    need it.  The proof is similar to that of [typing_weakening].
    HINT: You'll need to use [rewrite_env] to prepend [nil],
    and [simpl_env] to simplify nil away.
*)

Lemma typing_subst_simple : forall (E : env) e u S T (z : atom),
  typing ((z ~ S) ++ E) e T ->
  typing E u S ->
  typing E ([z ~> u] e) T.
Proof.
(* EXERCISE *) Admitted.

(*************************************************************************)
(** * Other structural properties *)
(*************************************************************************)

(* PFPL lists weakening and substitution, but there are two other important 
   structural properties of type systems: strengthening and exchange. *)


(* Challenge exercise [exchange]
   The exchange lemma states that the order of bindings in the typing 
   context doesn't matter.
  
   Hints:
     - Don't forget to use the [remember as] tactic.
     - The metalib tactic [solve_uniq] does what it claims.
     - There are 4 subcases in the fvar case: x is in G1, x is x1 or x2 or x is in G2
       access these four cases in succession using the lemma [binds_app_1].
     - [SearchAbout binds.] to see lemmas available for reasoning about 
       bindings in the context.
     - You'll need to rewrite_env to call the induction hypothesis in 
       the case for [exp_let].
*)


Lemma exchange : forall G1 G2 x1 x2 T1 T2 e T,
    typing (G1 ++ (x1 ~ T1) ++ (x2 ~ T2) ++ G2) e T ->
    typing (G1 ++ (x2 ~ T2) ++ (x1 ~ T1) ++ G2) e T.
Proof.
(* CHALLENGE EXERCISE *) Admitted.

(* Challenge exercise [strengthening]
   Strengthening means that variables that are not actually used in 
   an expression can be removed from the typing context.
  
   Hints:
     - The metalib tactic [solve_uniq] does what it claims.
     - [SearchAbout binds.] to see lemmas available for reasoning about 
       bindings in the context.
     - Don't forget about fv_open.
*)

Lemma strengthening : forall G e T,
    typing G e T
    -> forall G1 G2 x U, 
      G = G1 ++ (x ~ U) ++ G2 -> x `notin` fv e -> typing (G1 ++ G2) e T.
Proof.
(* CHALLENGE EXERCISE *) Admitted.




(*************************************************************************)
(** * Decomposition (Lemma 4.5) *)
(*************************************************************************)

(** Challenge Exercise [decomposition]
   Decomposition states that any (large) expression can be decomposed into a
   client and implementor by introducing a variable to mediate the
   interaction. 
   The proof of this lemma requires many of the lemmas shown above.
   Hint: prove this lemma by induction on the first typing judgement 
   (after appropriately generalizing it).
 *)
  
Lemma decomposition : forall e' e G x T',
    typing G ([ x ~> e ] e') T'->
    forall T, uniq ((x ~ T) ++ G) -> typing G e T -> typing ((x ~ T) ++ G) e' T'. 
Proof.
(* CHALLENGE EXERCISE *) Admitted.


(*************************************************************************)
(** * Renaming *)
(*************************************************************************)

(* Substitution and weakening together give us a property we call
   renaming: (see [typing_rename below] that we can change the name
   of the variable used to open an expression in a typing
   derivation. In practice, this means that if a variable is not
   "fresh enough" during a proof, we can use this lemma to rename it
   to one with additional freshness constraints.
   Renaming is used below to show the correspondence between the
   exists-fresh version of the rules with the cofinite version, and
   also to show that typechecking is decidable.
*)

(*
   However, before we prove renaming, we need an auxiliary lemma about
   typing judgments which says that terms are well-typed only in
   unique environments.
*)

Lemma typing_uniq : forall E e T,
  typing E e T -> uniq E.
Proof.
  intros E e T H.
  induction H; auto.
Qed.

(*
   Demo: the proof of renaming.
   Note that this proof does not proceed by induction: even if we add
   new typing rules to the language, as long as the weakening and
   substution properties hold we can use this proof.
*)
Lemma typing_rename : forall (x y : atom) E e T1 T2,
  x `notin` fv e -> y `notin` (dom E `union` fv e) ->
  typing ((x ~ T1) ++ E) (open e (exp_fvar x)) T2 ->
  typing ((y ~ T1) ++ E) (open e (exp_fvar y)) T2.
Proof.
  intros x y E e T1 T2 Fr1 Fr2 H.
  destruct (x == y).
  - Case "x = y".
    subst; eauto.
  - Case "x <> y".
    assert (J : uniq ((x ~ T1) ++ E)).
      eapply typing_uniq; eauto.
    assert (J' : uniq E).
      inversion J; eauto.
    rewrite (@subst_intro x); eauto.
    rewrite_env (nil ++ (y ~ T1) ++ E).
    apply typing_subst with (S := T1).
    simpl_env.
    + SCase "(open x s) is well-typed".
      apply typing_weakening_strengthened. eauto. auto.
    + SCase "y is well-typed".
      eapply typing_var; eauto.
Qed.


(*************************************************************************)
(** * Exists-Fresh Definitions *)
(*************************************************************************)

(* The use of cofinite quantification in the exp_let typing rule may make some
   people worry that we are not formalizing the "right" language.
   Furthermore, although this rule has a strong induction principle, it can be
   difficult to use it to *construct* typing derivations.
   Below, we show that an "exists-fresh" version of the rules is the same as
   the cofinite version, by showing that the "exists-fresh" typing rule for
   let is admissible.
   In otherwords, we will prove the lemma `typing_let_exists` below, which 
   states that we don't need to show that the body of the let expression type
   checks for all but a finite number of variables --- instead we only need to 
   show that it type checks for a single variable, as long as that variable is 
   suitably fresh. 
*)
 
Lemma typing_let_exists : forall x (E : env) (e1 e2 : exp) (T1 T2 : typ),
       typing E e1 T1 
       -> x `notin` fv e2
       -> typing ((x ~ T1) ++ E) (open e2 (exp_fvar x)) T2 
       -> typing E (exp_let e1 e2) T2.
Proof.
  intros x E e1 e2 T1 T2 Te1 Fr Te2.
  pick fresh y and apply typing_let.
  - eauto.
  - apply typing_rename with (x := x); auto.
Qed.

(* Similarly, we can use renaming to strengthen the inversion principle 
   that we get for typing an expression with binding. 
   The inversion principle that we want should say that the body of the 
   let is well-typed for any x that is not in the domain of the environment 
   or free in e2. 
*)

Lemma typing_let_inversion : forall (E : env) (e1 e2 : exp) (T2 : typ),
    typing E (exp_let e1 e2) T2
    -> (exists T1, typing E e1 T1 /\
      (forall x,  x `notin` (fv e2 \u dom E)
       -> typing ((x ~ T1) ++ E) (open e2 (exp_fvar x)) T2)).
Proof.
  intros E e1 e2 T2 H.
  inversion H. subst.
  (* This is the automatic inversion principle. Compare what we know now in H5 
     with the statment above. *)
  exists T1. split.
  - auto.
  - intros.
    pick fresh y.
    apply typing_rename with (x := y).
    auto.
    auto.
    apply H5. auto.
Qed.


(*************************************************************************)
(** * Decidability of Typechecking *)
(*************************************************************************)

(* Finally, we give another example of a proof that makes use of the
   renaming lemma. We show that determining whether a program type
   checks is decidable.
*)

(** Equality on types is decidable *)
Lemma eq_typ_dec : forall (T T' : typ),
  { T = T' } + { T <> T' }.
Proof.
  decide equality.
Qed.


(* A property P is decidable if we can show the proposition P \/ ~P. *)
Definition decidable (P : Prop) := (P \/ ~ P).

(* Demo: this proof puts together a lot of what we have seen in this section. *)

Lemma typing_decidable : forall E e,
  lc e -> uniq E -> decidable (exists T, typing E e T).
Proof.
  intros E e LC Uniq.
  generalize dependent E.
  induction LC; intros E Uniq.
  - Case "lc_var".
    destruct (@binds_lookup_dec _ x E) as [[T H] | H].
      SCase "variable is in environment".
      left; eauto.
      SCase "variable not in environment".
      right.  intros [T J]. inversion J; subst; eauto.
  - Case "lc_num".
    left. exists typ_num. auto.
  - Case "lc_str".
    left. exists typ_string. auto.
  - Case "lc_let".
    
    destruct (IHLC E Uniq) as [ [T He1] | NC].
    + SCase "rhs typechecks".
    (* To know whether the body typechecks, we must first
       pick a fresh variable to use the IH (aka HO).
    *)
    pick fresh x.
    assert (Fr' : x `notin` L) by auto.
    destruct (H0 x Fr' ((x ~ T) ++ E)) as [[S J] | J]; eauto.
    ++ SSCase "body typeable".
      left.
      exists S.
      eapply typing_let_exists; eauto.
   ++ SSCase "body not typeable".
      right.
      intros [S K].
      apply typing_let_inversion in K.
      destruct K as [T1 [Te1 Te2]].
      apply J.
      eapply (unicity _ _ _ He1) in Te1. subst.
      exists S.
      apply Te2. auto.
    + SCase "rhs not typeable".
      right.
      intros [S K].
      inversion K; subst.
      apply NC. exists T1. auto.
  -  Case "typing_op".
     destruct op0.
     destruct (IHLC1 E) as [[T H] | H]; eauto.
     -- SCase "first arg typeable".
     destruct (IHLC2 E) as [[S J] | J]; eauto.
        ++ SSCase "second arg typeable".
     destruct T; destruct S.
     + left. exists typ_num. auto.
     + right;
       intros [S' J'];
       inversion J'; subst;
       assert (K : typ_num = typ_string); eauto using unicity;
         inversion K.
     + right;
       intros [S' J'];
       inversion J'; subst;
       assert (K : typ_num = typ_string); eauto using unicity;
         inversion K.
     + right;
       intros [S' J'];
       inversion J'; subst;
       assert (K : typ_num = typ_string); eauto using unicity;
         inversion K.
     ++  SSCase "second argument not typeable".
        right. intros [S' J']. inversion J'; subst; eauto.
       -- SCase "first argument not typeable".
          right. intros [S' J']. inversion J'; subst; eauto.
       -- right. intros [S' J']. inversion J'; subst; eauto.
       -- right. intros [S' J']. inversion J'; subst; eauto.
Qed.