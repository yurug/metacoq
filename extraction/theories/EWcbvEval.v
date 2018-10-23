(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config utils Ast univ.
From TemplateExtraction Require Import EAst EInduction ELiftSubst EUnivSubst ETyping.
From Template Require AstUtils.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Existing Instance config.default_checker_flags.


(** * Weak (head) call-by-value evaluation strategy.

  The [wcbveval] inductive relation specifies weak cbv evaluation.  It
  is shown to be a subrelation of the 1-step reduction relation from
  which conversion is defined. Hence two terms that reduce to the same
  wcbv head normal form are convertible.

  This reduction strategy is supposed to mimick at the Coq level the
  reduction strategy of ML programming languages. It is used to state
  the extraction conjecture that can be applied to Coq terms to produce
  (untyped) terms where all proofs are erased to a dummy value. *)

(** ** Big step version of weak cbv beta-zeta-iota-fix-delta reduction.

  TODO: CoFixpoints *)

Section Wcbv.
  Context (Σ : global_declarations).
  (* The local context is fixed: we are only doing weak reductions *)

  Inductive eval : term -> term -> Prop :=
  (** Reductions *)
  | eval_box l : eval (mkApps tBox l) tBox

  (** Beta *)
  | eval_beta f na b a a' res :
      eval f (tLambda na b) ->
      eval a a' ->
      eval (subst10 a' b) res ->
      eval (tApp f a) res

  (** Let *)
  | eval_zeta na b0 b0' b1 res :
      eval b0 b0' ->
      eval (subst10 b0' b1) res ->
      eval (tLetIn na b0 b1) res

  (** Case *)
  | eval_iota ind pars discr c u args brs res :
      eval discr (mkApps (tConstruct ind c u) args) ->
      eval (iota_red pars c args brs) res ->
      eval (tCase (ind, pars) discr brs) res

  (** Fix unfolding, with guard *)
  | eval_fix mfix idx args args' narg fn res :
      unfold_fix mfix idx = Some (narg, fn) ->
      Forall2 eval args args' -> (* QUESTION should we reduce the args after the recursive arg here? *)
      is_constructor narg args' ->
      eval (mkApps fn args') res ->
      eval (mkApps (tFix mfix idx) args) res

  (** CoFix-case unfolding *)
  | red_cofix_case ip mfix idx args narg fn brs res :
      unfold_cofix mfix idx = Some (narg, fn) ->
      eval (tCase ip (mkApps fn args) brs) res ->
      eval (tCase ip (mkApps (tCoFix mfix idx) args) brs) res


  (** CoFix-proj unfolding *)
  | red_cofix_proj p mfix idx args narg fn res :
      unfold_cofix mfix idx = Some (narg, fn) ->
      eval (tProj p (mkApps fn args)) res ->
      eval (tProj p (mkApps (tCoFix mfix idx) args)) res

  (** Constant unfolding *)
  | eval_delta c decl body (isdecl : declared_constant Σ c decl) u res :
      decl.(cst_body) = Some body ->
      eval (subst_instance_constr u body) res ->
      eval (tConst c u) res

  (** Proj *)
  | eval_proj i pars arg discr args k u res :
      eval discr (mkApps (tConstruct i k u) args) ->
      eval (List.nth (pars + arg) args tDummy) res ->
      eval (tProj (i, pars, arg) discr) res

  (** Abstractions are values *)
  | eval_abs na N : eval (tLambda na N) (tLambda na N)

  (** Constructors applied to values are values *)
  | eval_constr f i k u l l' :
      eval f (tConstruct i k u) ->
      Forall2 eval l l' ->
      eval (mkApps f l) (mkApps (tConstruct i k u) l')

  (* | evar ev l l' : evals l l' -> eval (tEvar ev l) (tEvar ev l') *)
  | eval_evar ev l : eval (tEvar ev l) (tEvar ev l) (* Lets say it is a value for now *).

  (** The right induction principle for the nested [Forall] cases: *)

  Lemma eval_evals_ind :
    forall P : term -> term -> Prop,
      (forall l, P (mkApps tBox l) tBox) ->
      (forall (f : term) (na : name) (b a a' : term) (res : term),
          eval f (tLambda na b) ->
          P f (tLambda na b) ->
          eval a a' -> P a a' ->
          eval (b {0 := a'}) res -> P (b {0 := a'}) res -> P (tApp f a) res) ->

      (forall (na : name) (b0 b0' b1 res : term),
          eval b0 b0' -> P b0 b0' -> eval (b1 {0 := b0'}) res -> P (b1 {0 := b0'}) res ->
          P (tLetIn na b0 b1) res) ->

      (forall (ind : inductive) (pars : nat) (discr : term) (c : nat) (u : universe_instance)
              (args : list term) (brs : list (nat * term)) (res : term),
          eval discr (mkApps (tConstruct ind c u) args) ->
          P discr (mkApps (tConstruct ind c u) args) ->
          eval (iota_red pars c args brs) res ->
          P (iota_red pars c args brs) res -> P (tCase (ind, pars) discr brs) res) ->

      (forall (mfix : mfixpoint term) (idx : nat) (args args' : list term) (narg : nat) (fn res : term),
          unfold_fix mfix idx = Some (narg, fn) ->
          Forall2 eval args args' ->
          Forall2 P args args' ->
          is_constructor narg args' = true ->
          eval (mkApps fn args') res -> P (mkApps fn args') res -> P (mkApps (tFix mfix idx) args) res) ->

      (forall (ip : inductive * nat)  (mfix : mfixpoint term) (idx : nat) (args : list term)
              (narg : nat) (fn : term) (brs : list (nat * term)) (res : term),
          unfold_cofix mfix idx = Some (narg, fn) ->
          eval (tCase ip (mkApps fn args) brs) res ->
          P (tCase ip (mkApps fn args) brs) res -> P (tCase ip (mkApps (tCoFix mfix idx) args) brs) res) ->

      (forall (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn res : term),
          unfold_cofix mfix idx = Some (narg, fn) ->
          eval (tProj p (mkApps fn args)) res ->
          P (tProj p (mkApps fn args)) res -> P (tProj p (mkApps (tCoFix mfix idx) args)) res) ->

      (forall (c : ident) (decl : constant_body) (body : term),
          declared_constant Σ c decl ->
          forall (u : universe_instance) (res : term),
            cst_body decl = Some body ->
            eval (subst_instance_constr u body) res -> P (subst_instance_constr u body) res -> P (tConst c u) res) ->

      (forall (i : inductive) (pars arg : nat) (discr : term) (args : list term) (k : nat)
              (u : universe_instance) (res : term),
          eval discr (mkApps (tConstruct i k u) args) ->
          P discr (mkApps (tConstruct i k u) args) ->
          eval (nth (pars + arg) args tDummy) res ->
          P (nth (pars + arg) args tDummy) res -> P (tProj (i, pars, arg) discr) res) ->

      (forall (na : name) (M N : term), P (tLambda na N) (tLambda na N)) ->

      (forall (f8 : term) (i : inductive) (k : nat) (u : universe_instance) (l l' : list term),
          eval f8 (tConstruct i k u) ->
          P f8 (tConstruct i k u) -> Forall2 eval l l' -> Forall2 P l l' -> P (mkApps f8 l) (mkApps (tConstruct i k u) l')) ->

      (forall (ev : nat) (l : list term), P (tEvar ev l) (tEvar ev l)) ->

      forall t t0 : term, eval t t0 -> P t t0.
  Proof.
    intros P Hbox Hbeta Hlet Hcase Hfix Hcoficase Hcofixproj
           Hconst Hproj Hlam Hcstr Hevar.
    fix eval_evals_ind 3. destruct 1;
             try match goal with [ H : _ |- _ ] =>
                             match type of H with
                               forall t t0, eval t t0 -> _ => fail 1
                             | _ => eapply H
                             end end; eauto.
    clear H1 H2.
    revert args args' H0. fix aux 3. destruct 1. constructor; auto.
    constructor. now apply eval_evals_ind. now apply aux.
    revert l l' H0. fix aux 3. destruct 1; constructor.
    now apply eval_evals_ind. apply aux. auto.
  Defined.

  (** Characterization of values for this reduction relation:
      Basically atoms (constructors, inductives, products (FIXME sorts missing))
      and de Bruijn variables and lambda abstractions. Closed values disallow
      de Bruijn variables. *)

  Inductive value : term -> Prop :=
  | value_tBox : value tBox
  | value_tEvar ev l : value (tEvar ev l)
  | value_tLam na b : value (tLambda na b)
  | value_tConstruct i k u l : List.Forall value l -> value (mkApps (tConstruct i k u) l).

  Lemma value_values_ind : forall P : term -> Prop,
      (P tBox) ->
       (forall i : nat, P (tRel i)) ->
       (forall (ev : nat) (l : list term), P (tEvar ev l)) ->
       (forall (na : name) (b : term), P (tLambda na b)) ->
       (forall (i : inductive) (k : nat) (u : universe_instance) (l : list term),
           List.Forall value l -> List.Forall P l -> P (mkApps (tConstruct i k u) l)) ->
       forall t : term, value t -> P t.
  Proof.
    intros P ?????.
    fix value_values_ind 2. destruct 1. 1-3:clear value_values_ind; auto.
    apply H3. apply H4.
    revert l H4. fix aux 2. destruct 1. constructor; auto.
    constructor. now apply value_values_ind. now apply aux.
  Defined.

  (** The codomain of evaluation is only values:
      It means no redex can remain at the head of an evaluated term. *)

  Lemma eval_to_value e e' : eval e e' -> value e'.
  Proof.
    induction 1 using eval_evals_ind; simpl; auto using value.
    eapply (value_tConstruct i k u).
    apply (Forall2_right _ _ _ H1).
  Qed.

  (** Evaluation preserves closedness: *)
  Lemma eval_closed : forall n t u, closedn n t = true -> eval t u -> closedn n u = true.
  Proof.
    induction 2 using eval_evals_ind; simpl in *; eauto. eapply IHeval3.
    admit.
  Admitted. (* FIXME complete *)

End Wcbv.