(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From Template Require Import config univ monad_utils utils BasicAst AstUtils UnivSubst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICSR PCUICGeneration PCUICValidity PCUICWeakening PCUICSafeReduce.

Import MonadNotation.

(* from Validity.v *)
Existing Instance config.default_checker_flags.

Axiom todo : forall {A}, A.

Arguments weakening {_ _ _} _ {_ _}.

Notation wf_local_rel Σ Γ Γ'
  := (All_local_env (lift_typing (fun Σ0 Γ0 t T => Σ0 ;;; Γ ,,, Γ0 |- t : T) Σ) Γ').

Arguments localenv_nil {_}.
Arguments localenv_cons_def {_ _ _ _ _} _ _.
Arguments localenv_cons_abs {_ _ _ _} _ _.
Arguments All_nil {_ _}.
Arguments All_cons {_ _ _ _}.


Definition wf_local_rel_app {Σ Γ1 Γ2 Γ3} :
  wf_local_rel Σ Γ1 Γ2 -> wf_local_rel Σ (Γ1 ,,, Γ2) Γ3
  -> wf_local_rel Σ Γ1 (Γ2 ,,, Γ3).
Proof.
  intros H1 H2. eapply All_local_env_app_inv.
  split. assumption.
  eapply All_local_env_impl. eassumption.
  intros Γ t []; cbn;
    now rewrite app_context_assoc. 
Defined.


Lemma eq_ind_spec x y : reflect (x = y) (eq_ind x y).
  destruct x as [ind i], y as [ind' i'].
  unfold eq_ind; cbn.
Admitted.

Notation "( x ; y )" := (@existT _ _ x y).
Notation "( x ; y ; z )" := (x; (y; z)).
Notation "( x ; y ; z ; u )" := (x; (y; (z; u))).
Notation "x .1" := (@projT1 _ _ x) (at level 3, format "x '.1'").
Notation "x .2" := (@projT2 _ _ x) (at level 3, format "x '.2'").

Fixpoint monad_All {T} {M : Monad T} {A} {P} (f : forall x, T (P x)) l : T (@All A P l)
  := match l with
     | [] => ret All_nil
     | a :: l => X <- f a ;;
                Y <- monad_All f l ;;
                ret (All_cons X Y)
     end.

Fixpoint monad_All2 {T E} {M : Monad T} {M' : MonadExc E T} wrong_sizes
         {A B R} (f : forall x y, T (R x y)) l1 l2
  : T (@All2 A B R l1 l2)
  := match l1, l2 with
     | [], [] => ret (All2_nil R)
     | a :: l1, b :: l2 => X <- f a b ;;
                          Y <- monad_All2 wrong_sizes f l1 l2 ;;
                          ret (All2_cons R a b l1 l2 X Y)
     | _, _ => raise wrong_sizes
     end.

Definition monad_prod {T} {M : Monad T} {A B} (x : T A) (y : T B): T (A * B)%type
  := X <- x ;; Y <- y ;; ret (X, Y).

Definition check_dec {T E} {M : Monad T} {M' : MonadExc E T} (e : E) {P}
           (H : {P} + {~ P})
  : T P
  := match H with
     | left x => ret x
     | right _ => raise e
     end.

Definition check_eq_true {T E} {M : Monad T} {M' : MonadExc E T} b (e : E)
  : T (b = true)
  := if b return T (b = true) then ret eq_refl else raise e.


Definition mkApps_decompose_app_rec t l :
  mkApps t l = mkApps  (fst (decompose_app_rec t l)) (snd (decompose_app_rec t l)).
Proof.
  revert l; induction t; try reflexivity.
  intro l; cbn in *.
  transitivity (mkApps t1 ((t2 ::l))). reflexivity.
  now rewrite IHt1.
Qed.

Definition mkApps_decompose_app t :
  t = mkApps  (fst (decompose_app t)) (snd (decompose_app t))
  := mkApps_decompose_app_rec t [].

Derive EqDec for sort_family.
Next Obligation.
  unfold Classes.dec_eq. decide equality.
Defined.


Lemma inversion_Prod {cf: checker_flags} :
  forall {Σ Γ na A B T},
    Σ ;;; Γ |- tProd na A B : T ->
      exists s1 s2,
        ∥ Σ ;;; Γ |- A : tSort s1 ∥ /\
        ∥ Σ ;;; Γ ,, vass na A |- B : tSort s2 ∥ /\
        ∥ Σ ;;; Γ |- tSort (Universe.sort_of_product s1 s2) <= T ∥.
Proof.
(*   intros Σ Γ na A B T X.  dependent induction X. *)
(*   - exists s1, s2. split ; [| split]. *)
(*     + constructor. assumption. *)
(*     + constructor. assumption. *)
(*     + constructor. apply cumul_refl'. *)
(*   - destruct (IHX1 _ _ _ eq_refl) as [s1 [s2 [? [? ?]]]]. *)
(*     exists s1, s2. split ; [| split]. *)
(*     + assumption. *)
(*     + assumption. *)
(*     + destruct H1. constructor. eapply cumul_trans ; eassumption. *)
(* Qed. *)
Admitted.

Inductive type_error :=
| UnboundRel (n : nat)
| UnboundVar (id : string)
| UnboundMeta (m : nat)
| UnboundEvar (ev : nat)
| UndeclaredConstant (c : string)
| UndeclaredInductive (c : inductive)
| UndeclaredConstructor (c : inductive) (i : nat)
| NotConvertible (Γ : context) (t u t' u' : term)
| NotASort (t : term)
| NotAProduct (t t' : term)
| NotAnInductive (t : term)
| IllFormedFix (m : mfixpoint term) (i : nat)
| UnsatisfiedConstraints (c : ConstraintSet.t)
| Msg (s : string).

Definition NotConvertible' Γ t u := NotConvertible Γ t u t u.

Lemma lookup_env_id Σ id decl
  : lookup_env Σ id = Some decl -> id = global_decl_ident decl.
Proof.
  induction Σ; cbn. inversion 1.
  destruct (ident_eq_spec id (global_decl_ident a)).
  - inversion 1. now destruct H1.
  - easy.
Qed.



Local Open Scope string_scope.
Definition string_of_list_aux {A} (f : A -> string) (l : list A) : string :=
  let fix aux l :=
      match l return string with
      | nil => ""
      | cons a nil => f a
      | cons a l => f a ++ "," ++ aux l
      end
  in aux l.

Definition string_of_list {A} (f : A -> string) (l : list A) : string :=
  "[" ++ string_of_list_aux f l ++ "]".

Definition string_of_level (l : Level.t) : string :=
  match l with
  | Level.lProp => "Prop"
  | Level.lSet => "Set"
  | Level.Level s => s
  | Level.Var n => "Var" ++ string_of_nat n
  end.

Definition string_of_level_expr (l : Level.t * bool) : string :=
  let '(l, b) := l in
  string_of_level l ++ (if b then "+1" else "").

Definition string_of_sort (u : universe) :=
  string_of_list string_of_level_expr u.
Definition string_of_name (na : name) :=
  match na with
  | nAnon => "Anonymous"
  | nNamed n => n
  end.
Definition string_of_universe_instance u :=
  string_of_list string_of_level u.

Definition string_of_def {A : Set} (f : A -> string) (def : def A) :=
  "(" ++ string_of_name (dname def) ++ "," ++ f (dtype def) ++ "," ++ f (dbody def) ++ ","
      ++ string_of_nat (rarg def) ++ ")".

Definition string_of_inductive (i : inductive) :=
  (inductive_mind i) ++ "," ++ string_of_nat (inductive_ind i).

Fixpoint string_of_term (t : term) :=
  match t with
  | tRel n => "Rel(" ++ string_of_nat n ++ ")"
  | tVar n => "Var(" ++ n ++ ")"
  | tMeta n => "Meta(" ++ string_of_nat n ++ ")"
  | tEvar ev args => "Evar(" ++ string_of_nat ev ++ "[]" (* TODO *)  ++ ")"
  | tSort s => "Sort(" ++ string_of_sort s ++ ")"
  | tProd na b t => "Prod(" ++ string_of_name na ++ "," ++
                            string_of_term b ++ "," ++ string_of_term t ++ ")"
  | tLambda na b t => "Lambda(" ++ string_of_name na ++ "," ++ string_of_term b
                                ++ "," ++ string_of_term t ++ ")"
  | tLetIn na b t' t => "LetIn(" ++ string_of_name na ++ "," ++ string_of_term b
                                 ++ "," ++ string_of_term t' ++ "," ++ string_of_term t ++ ")"
  | tApp f l => "App(" ++ string_of_term f ++ "," ++ string_of_term l ++ ")"
  | tConst c u => "Const(" ++ c ++ "," ++ string_of_universe_instance u ++ ")"
  | tInd i u => "Ind(" ++ string_of_inductive i ++ "," ++ string_of_universe_instance u ++ ")"
  | tConstruct i n u => "Construct(" ++ string_of_inductive i ++ "," ++ string_of_nat n ++ ","
                                    ++ string_of_universe_instance u ++ ")"
  | tCase (ind, i) t p brs =>
    "Case(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_term t ++ ","
            ++ string_of_term p ++ "," ++ string_of_list (fun b => string_of_term (snd b)) brs ++ ")"
  | tProj (ind, i, k) c =>
    "Proj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
            ++ string_of_term c ++ ")"
  | tFix l n => "Fix(" ++ (string_of_list (string_of_def string_of_term) l) ++ "," ++ string_of_nat n ++ ")"
  | tCoFix l n => "CoFix(" ++ (string_of_list (string_of_def string_of_term) l) ++ "," ++ string_of_nat n ++ ")"
  end.

Definition string_of_type_error (e : type_error) : string :=
  match e with
  | UnboundRel n => "Unboound rel " ++ string_of_nat n
  | UnboundVar id => "Unbound var " ++ id
  | UnboundMeta m => "Unbound meta " ++ string_of_nat m
  | UnboundEvar ev => "Unbound evar " ++ string_of_nat ev
  | UndeclaredConstant c => "Undeclared constant " ++ c
  | UndeclaredInductive c => "Undeclared inductive " ++ (inductive_mind c)
  | UndeclaredConstructor c i => "Undeclared inductive " ++ (inductive_mind c)
  | NotConvertible Γ t u t' u' => "Terms are not convertible: " ++
      string_of_term t ++ " " ++ string_of_term u ++ " after reduction: " ++
      string_of_term t' ++ " " ++ string_of_term u'
  | NotASort t => "Not a sort"
  | NotAProduct t t' => "Not a product"
  | NotAnInductive t => "Not an inductive"
  | IllFormedFix m i => "Ill-formed recursive definition"
  | UnsatisfiedConstraints c => "Unsatisfied constraints"
  | Msg s => "Msg" ++ s
  end.

Inductive typing_result (A : Type) :=
| Checked (a : A)
| TypeError (t : type_error).
Global Arguments Checked {A} a.
Global Arguments TypeError {A} t.

Instance typing_monad : Monad typing_result :=
  {| ret A a := Checked a ;
     bind A B m f :=
       match m with
       | Checked a => f a
       | TypeError t => TypeError t
       end
  |}.

Instance monad_exc : MonadExc type_error typing_result :=
  { raise A e := TypeError e;
    catch A m f :=
      match m with
      | Checked a => m
      | TypeError t => f t
      end
  }.


Axiom check_conv_leq : forall {cf: checker_flags},
    global_context -> context -> term -> term -> typing_result unit.
Axiom check_conv     : forall {cf: checker_flags},
    global_context -> context -> term -> term -> typing_result unit.


Conjecture conv_spec : forall `{checker_flags} {F:Fuel} Σ Γ t u,
    ∥ Σ ;;; Γ |- t = u ∥ <-> check_conv Σ Γ t u = Checked ().

Conjecture cumul_spec : forall `{checker_flags} {F:Fuel} Σ Γ t u,
    ∥ Σ ;;; Γ |- t <= u ∥ <-> check_conv_leq Σ Γ t u = Checked ().

(* Conjecture reduce_cumul : *)
(*   forall `{checker_flags} Σ Γ n t, Σ ;;; Γ |- try_reduce (fst Σ) Γ n t <= t. *)

Section Typecheck.
  Context {Σ : global_context} {HΣ : wf Σ}.

  Definition cumul_red_l' (Γ : context) (t u : term)
    : red (fst Σ) Γ t u -> Σ;;; Γ |- t <= u.
  Proof.
    induction 1. eapply cumul_refl'.
    eapply cumul_trans. eassumption.
    eapply cumul_red_l. eassumption.
    eapply cumul_refl'.
  Defined.

  (* This is not the correct validity lemma ... *)
  Lemma istype_type:
    forall (Γ : context) t A, Σ ;;; Γ |- t : A -> {s & Σ ;;; Γ |- A : tSort s}.
  Proof.
  Admitted.

  Lemma welltyped_type:
    forall (Γ : context) t A, Σ;;; Γ |- t : A -> welltyped Σ Γ A.
  Proof.
    intros Γ t A X. econstructor. exact (istype_type _ _ _ X).2.
  Defined.

  Lemma validity_term {Γ t T} :
    wf_local Σ Γ -> Σ ;;; Γ |- t : T -> isWfArity_or_Type Σ Γ T.
  Proof.
    intros. eapply validity; eassumption.
  Defined.

  Lemma isWfArity_red1 {Γ A B} :
    red1 (fst Σ) Γ A B -> isWfArity typing Σ Γ A -> isWfArity typing Σ Γ B.
  Proof.
    induction 1; intros [ctx [s [H1 H2]]]; try (now inversion H1).
    - cbn in H1. exists ctx, s. split; [|assumption]. admit.
    - admit.
    - cbn in H1. exists ctx, s. split; [|assumption]. cbn. admit.
  Admitted.

  Lemma isWfArity_red {Γ A B} :
    red (fst Σ) Γ A B -> isWfArity typing Σ Γ A -> isWfArity typing Σ Γ B.
  Proof.
    induction 1. easy. intro; now eapply isWfArity_red1.
  Qed.

  Lemma type_reduction {Γ t A B}
    : wf_local Σ Γ -> Σ ;;; Γ |- t : A -> red (fst Σ) Γ A B -> Σ ;;; Γ |- t : B.
  Proof.
    intros HΓ Ht Hr.
    econstructor. eassumption.
    2: now eapply cumul_red_l'.
    destruct (validity_term HΓ Ht).
    - left. eapply isWfArity_red; eassumption.
    - destruct i as [s HA]. right.
      exists s. eapply PCUICSR.subject_reduction; eassumption.
  Defined.

  Definition hnf Γ t (h : welltyped Σ Γ t) :=
    reduce_stack RedFlags.default Σ Γ t Empty h.

  (* Should be in Prop ... *)
  Theorem hnf_sound {Γ t h} : red (fst Σ) Γ t (zip (hnf Γ t h)).
  Admitted.
  (* Proof. *)
    (* exact (reduce_stack_sound RedFlags.default Σ Γ t Empty h). *)
  (* Defined. *)

  Program Definition reduce_to_sort Γ t (h : welltyped Σ Γ t)
    : typing_result ({u : universe & red (fst Σ) Γ t (tSort u)}) :=
    match t with
    | tSort s => ret (s; refl_red _ _ _)
    | _ =>
      match hnf Γ t h with
      | (tSort s, Empty) => ret (s; _)
      | _ => raise (NotASort t)
      end
    end.
  Next Obligation.
    pose proof (hnf_sound (h:=h)).
    now rewrite <- Heq_anonymous in X.
  Defined.

  Program Definition reduce_to_prod Γ t (h : welltyped Σ Γ t)
       : typing_result ({ na & {a & {b & red (fst Σ) Γ t (tProd na a b)}}}) :=
    match t with
    | tProd na a b => ret (na; a; b; refl_red _ _ _)
    | _ =>
      match hnf Γ t h with
      | (tProd na a b, Empty) => ret (na; a; b; _)
      | t' => raise (NotAProduct t (zip t'))
      end
    end.
  Next Obligation.
    pose proof (hnf_sound (h:=h)).
    now rewrite <- Heq_anonymous in X.
  Defined.

  Fixpoint stack_to_apps π : typing_result (list term) :=
    match π with
    | Empty => ret []
    | App t π => l <- stack_to_apps π ;; ret (t :: l)
    | _ => raise (Msg "not some applications")
    end.

  Lemma zip_stack_to_apps t π l :
    stack_to_apps π = Checked l -> zipc t π = mkApps t l.
  Proof.
    revert t l. induction π; cbn; try inversion 1.
    reflexivity.
    destruct (stack_to_apps π); inversion H1.
    erewrite IHπ; reflexivity.
  Qed.


  Program Definition reduce_to_ind Γ t (h : welltyped Σ Γ t)
    : typing_result ({ i & {u & {l & red (fst Σ) Γ t (mkApps (tInd i u) l)}}}) :=
    match decompose_app t with
    | (tInd i u, l) => ret (i; u; l; _)
    | _ =>
      match hnf Γ t h with
      | (tInd i u, π) => match stack_to_apps π with
                        | Checked l => ret (i; u; l; _)
                        | TypeError e => raise e
                        end
      | _ => raise (NotAnInductive t)
      end
    end.
  Next Obligation.
    assert (X : mkApps (tInd i u) l = t); [|rewrite X; apply refl_red].
    etransitivity. 2: symmetry; eapply mkApps_decompose_app.
    pose proof (f_equal fst Heq_anonymous) as X; cbn in X; rewrite X; clear X.
    pose proof (f_equal snd Heq_anonymous) as X; cbn in X; rewrite X; clear X.
    reflexivity.
  Defined.
  Next Obligation.
    pose proof (hnf_sound (h:=h)).
    rewrite <- Heq_anonymous1 in X.
    now erewrite <- zip_stack_to_apps.
  Defined.


  Program Definition convert_leq Γ (t u : term) : typing_result (Σ ;;; Γ |- t <= u) :=
    if eq_term (snd Σ) t u then ret _
    else _.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.

      (* match isconv Σ fuel Cumul Γ t [] u [] with *)
      (* | Some b => *)
      (*   if b then ret () *)
      (*   else raise (NotConvertible Γ t u t u) *)
      (* | None => (* fallback *) *)
      (*   t' <- reduce (fst Σ) Γ t ;; *)
      (*   u' <- reduce (fst Σ) Γ u ;; *)
      (*   if leq_term (snd Σ) t' u' then ret () *)
      (*   else raise (NotConvertible Γ t u t' u') *)
      (* end. *)

  Section InferAux.
    Variable (infer : forall Γ (HΓ : wf_local Σ Γ) (t : term),
                 typing_result ({ A : term & Σ ;;; Γ |- t : A })).

    Definition infer_type Γ HΓ t
      : typing_result ({u : universe & Σ ;;; Γ |- t : tSort u}) :=
      tx <- infer Γ HΓ t ;;
      u <- reduce_to_sort Γ tx.1 (welltyped_type _ _ _ tx.2) ;;
      ret (u.1; todo).

    Definition infer_cumul Γ HΓ t A : typing_result (Σ ;;; Γ |- t : A) :=
      A' <- infer Γ HΓ t ;;
      X <- convert_leq Γ A'.1 A ;;
      ret todo.
  End InferAux.


  Program Definition lookup_ind_decl ind
    : typing_result
        ({decl & {body & declared_inductive (fst Σ) decl ind body}}) :=
    match lookup_env (fst Σ) ind.(inductive_mind) with
    | Some (InductiveDecl _ decl) =>
      match nth_error decl.(ind_bodies) ind.(inductive_ind) with
      | Some body => ret (decl; body; _)
      | None => raise (UndeclaredInductive ind)
      end
    | _ => raise (UndeclaredInductive ind)
    end.
  Next Obligation.
    split.
    - symmetry in Heq_anonymous0.
      etransitivity. eassumption.
      erewrite (lookup_env_id _ _ _ Heq_anonymous0); reflexivity.
    - now symmetry.
  Defined.

  Definition check_consistent_constraints cstrs u
    : typing_result (consistent_universe_context_instance Σ cstrs u) :=
    match cstrs as cstrs' return (cstrs' = cstrs -> typing_result (consistent_universe_context_instance Σ cstrs' u)) with
    | Monomorphic_ctx ctx => fun _ => ret I
    | Polymorphic_ctx (t, c)
    | Cumulative_ctx ((t, c), _) => fun _ =>
        (if #|t| =? #|u| as b return (b = (#|t| =? #|u|) -> typing_result (#|t| = #|u| /\ check_constraints (snd Σ) (subst_instance_cstrs u c) = true))
         then fun Heqb =>
           (if check_constraints (snd Σ) (subst_instance_cstrs u c) as b
               return (b = check_constraints (snd Σ) (subst_instance_cstrs u c) -> typing_result (#|t| = #|u| /\ b = true))
            then fun _ => ret (conj (beq_nat_eq #|t| #|u| Heqb) eq_refl)
            else fun _ => raise (UnsatisfiedConstraints (subst_instance_cstrs u c)))
             eq_refl
         else
           fun _ => raise (UnboundVar "wrong length of instance"))
          eq_refl
    end eq_refl.

  Definition try_suc (u : Universe.t) : Universe.t :=   (* FIXME suc s *)
    map (fun '(l, b) =>  (l, true)) u.

  Definition to_wt Γ t
    : { A : term | ∥ Σ ;;; Γ |- t : A ∥ } -> welltyped Σ Γ t.
  Proof.
    intros [A [h]]. now exists A.
  Defined.

  Definition fix_context_i i mfix :=
    List.rev (mapi_rec (fun i (d : BasicAst.def term)
                        => vass (dname d) ((lift0 i) (dtype d))) mfix i).

  Program Fixpoint infer (Γ : context) (HΓ : wf_local Σ Γ) (t : term) {struct t}
    : typing_result ({ A : term & Σ ;;; Γ |- t : A }) :=
    match t with
    | tRel n =>
          match nth_error Γ n with
          | Some c => ret ((lift0 (S n)) (decl_type c); _)
          | None   => raise (UnboundRel n)
          end

    | tVar n  => raise (UnboundVar n)
    | tMeta n => raise (UnboundMeta n)
    | tEvar ev args => raise (UnboundEvar ev)

    | tSort u =>
          match u with
          | [ (l, false) ] =>
            ret (tSort (Universe.super l); _)
          | _ => raise (UnboundVar "not alg univ")
          end

    | tProd na A B =>
          s1 <- infer_type infer Γ HΓ A ;;
          s2 <- infer_type infer (Γ ,, vass na A) _ B ;;
          ret (tSort (Universe.sort_of_product s1.1 s2.1); _)

    | tLambda na A t =>
          s1 <- infer_type infer Γ HΓ A ;;
          B <- infer (Γ ,, vass na A) _ t ;;
          ret (tProd na A B.1; _)

    | tLetIn n b b_ty b' =>
          infer_type infer Γ HΓ b_ty ;;
          infer_cumul infer Γ HΓ b b_ty ;;
          b'_ty <- infer (Γ ,, vdef n b b_ty) _ b' ;;
          ret (tLetIn n b b_ty b'_ty.1; _)

    | tApp t u =>
          ty <- infer Γ HΓ t ;;
          pi <- reduce_to_prod Γ ty.1 _ ;;
          infer_cumul infer Γ HΓ u pi.2.1 ;;
          ret (subst10 u pi.2.2.1; _)

    | tConst cst u =>
          match lookup_env (fst Σ) cst with
          | Some (ConstantDecl _ d) =>
            check_consistent_constraints d.(cst_universes) u ;;
            let ty := subst_instance_constr u d.(cst_type) in
            ret (ty; _)
          |  _ => raise (UndeclaredConstant cst)
          end

    | tInd ind u =>
          d <- lookup_ind_decl ind ;;
          check_consistent_constraints d.1.(ind_universes) u ;;
          let ty := subst_instance_constr u d.2.1.(ind_type) in
          ret (ty; _)

    | tConstruct ind k u =>
          d <- lookup_ind_decl ind ;;
          match nth_error d.2.1.(ind_ctors) k with
          | Some cdecl =>
            check_consistent_constraints d.1.(ind_universes) u ;;
            ret (type_of_constructor d.1 cdecl (ind, k) u; _)
          | None => raise (UndeclaredConstructor ind k)
          end

    | tCase (ind, par) p c brs => 
      ty <- infer Γ HΓ c ;;
      I <- reduce_to_ind Γ ty.1 _ ;;
      let '(ind'; I') := I in let '(u; I'') := I' in let '(args; H) := I'' in
      check_eq_true (eq_ind ind ind')
                    (NotConvertible' Γ (tInd ind u) (tInd ind' u)) ;;
      d <- lookup_ind_decl ind' ;;
      let '(decl; d') := d in let '(body; HH) := d' in
      check_eq_true (ind_npars decl =? par)
                    (Msg "not the right number of parameters") ;;
      pty <- infer Γ HΓ p ;;
      match types_of_case ind decl body (firstn par args) u p pty.1 with
      | None => raise (Msg "not the type of a case")
      | Some (indctx, pctx, ps, btys) =>
        check_eq_true
          (check_correct_arity (snd Σ) body ind u indctx (firstn par args) pctx)
          (Msg "not correct arity") ;;
        infer_cumul infer Γ HΓ c (mkApps (tInd ind u) args) ;;
        match Exists_dec (fun sf  => universe_family ps = sf) (ind_kelim body)
                         (sort_family_eqdec _) with
        | right _ => raise (Msg "cannot eliminate over this sort")
        | left x => (fix check_branches (brs btys : list (nat * term)) {struct brs}
                    : typing_result (  All2
    (fun x0 y : nat * term => ((fst x0 = fst y) * (Σ;;; Γ |- snd x0 : snd y))%type)
    brs btys
)
                    := match brs, btys with
                       | [], [] => ret (All2_nil _)
                       | (n, t) :: brs , (m, A) :: btys =>
                         W <- check_dec (Msg "not nat eq") (EqDecInstances.nat_eqdec n m) ;;
                         Z <- infer_cumul infer Γ HΓ t A ;;
                         X <- check_branches brs btys ;;
                         ret (All2_cons _ _ _ _ _ (pair _ _) X)
                       | [], _ :: _
                       | _ :: _, [] => raise (Msg "wrong number of branches")
                       end) brs btys ;;

          (* monad_All2  *)
          (*            (fun x y => monad_prod (check_dec (Msg "not nat eq") *)
          (*                                           (nat_eqdec (fst x) (fst y))) *)
          (*                                (infer_cumul infer Γ HΓ (snd x) (snd y))) *)
          (*            brs btys ;; *)
          ret (mkApps p (List.skipn par args ++ [c]); _)
        end
      end

    | tProj (ind, n, k) c =>
          d <- lookup_ind_decl ind ;;
          match nth_error d.2.1.(ind_projs) k with
          | Some pdecl =>
            c_ty <- infer Γ HΓ c ;;
            I <- reduce_to_ind Γ c_ty.1 _ ;;
            let '(ind'; I') := I in let '(u; I'') := I' in let '(args; H) := I'' in
            check_eq_true (eq_ind ind ind')
                          (NotConvertible' Γ (tInd ind u) (tInd ind' u)) ;;
            check_eq_true (#|args| =? ind_npars d.1)
                          (Msg "not the right number of parameters") ;;
            let ty := snd pdecl in
            ret (subst0 (c :: List.rev args) (subst_instance_constr u ty);
                   _)
          | None => raise (Msg "projection not found")
          end

    | tFix mfix n =>
      match nth_error mfix n with
      | None => raise (IllFormedFix mfix n)
      | Some decl =>
        XX <- (fix check_types (mfix : mfixpoint term) acc (Hacc : wf_local_rel Σ Γ acc) {struct mfix}
              : typing_result (wf_local_rel Σ (Γ ,,, acc) (fix_context_i #|acc| mfix))
              := match mfix with
                 | [] => ret localenv_nil
                 | def :: mfix =>
       (* probably not tail recursive but needed so that next line terminates *)
                   W <- infer_type infer Γ HΓ (dtype def) ;;
                   let W' := weakening acc _ _ W.2 in
                   Z <- check_types mfix
                     (acc ,, vass (dname def) ((lift0 #|acc|) (dtype def)))
                     (localenv_cons_abs Hacc (W.1; W')) ;;
                   ret (wf_local_rel_app
                          (localenv_cons_abs localenv_nil (W.1; W')) Z)
                 end)
           mfix [] localenv_nil;;
        YY <- (fix check_bodies (mfix' : mfixpoint term) {struct mfix'}
 : typing_result (All (fun d =>
   (Σ ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d)) 
   * (isLambda (dbody d) = true))%type mfix')
              := match mfix' with
                 | [] => ret All_nil
                 | def :: mfix' =>
                   W1 <- infer_cumul infer (Γ ,,, fix_context mfix) _ (dbody def)
                                    (lift0 #|fix_context mfix| (dtype def)) ;;
                   W2 <- check_eq_true (isLambda (dbody def))
                                      (UnboundVar "not a lambda") ;;
                   Z <- check_bodies mfix' ;;
                   ret (All_cons (pair W1 W2) Z)
                 end) mfix ;;
        ret (dtype decl; type_Fix Σ Γ mfix n decl (eq_sym _)
               (All_local_env_app_inv _ Γ (fix_context mfix) (HΓ, XX)) YY)
      end


    | tCoFix mfix n =>
      match nth_error mfix n with
      | None => raise (IllFormedFix mfix n)
      | Some decl =>
        XX <- (fix check_types (mfix : mfixpoint term) acc (Hacc : wf_local_rel Σ Γ acc) {struct mfix}
              : typing_result (wf_local_rel Σ (Γ ,,, acc) (fix_context_i #|acc| mfix))
              := match mfix with
                 | [] => ret localenv_nil
                 | def :: mfix =>
       (* probably not tail recursive but needed so that next line terminates *)
                   W <- infer_type infer Γ HΓ (dtype def) ;;
                   let W' := weakening acc _ _ W.2 in
                   Z <- check_types mfix
                     (acc ,, vass (dname def) ((lift0 #|acc|) (dtype def)))
                     (localenv_cons_abs Hacc (W.1; W')) ;;
                   ret (wf_local_rel_app
                          (localenv_cons_abs localenv_nil (W.1; W')) Z)
                 end)
           mfix [] localenv_nil;;
        YY <- (fix check_bodies (mfix' : mfixpoint term) {struct mfix'}
              : typing_result (All (fun d => Σ ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d)) mfix')
              := match mfix' with
                 | [] => ret All_nil
                 | def :: mfix' =>
                   W1 <- infer_cumul infer (Γ ,,, fix_context mfix) _ (dbody def)
                                    (lift0 #|fix_context mfix| (dtype def)) ;;
                   Z <- check_bodies mfix' ;;
                   ret (All_cons W1 Z)
                 end) mfix ;;
        ret (dtype decl; type_CoFix Σ Γ mfix n decl (eq_sym _)
               (All_local_env_app_inv _ Γ (fix_context mfix) (HΓ, XX)) YY)
      end
    end.

  
  Next Obligation. now econstructor. Defined.
  Next Obligation. now econstructor. Defined.
  (* tProd *)
  Next Obligation. econstructor; cbn; easy. Defined.
  Next Obligation. econstructor; eassumption. Defined.
  (* tLambda *)
  Next Obligation. econstructor; cbn; easy. Defined.
  Next Obligation. econstructor; eassumption. Defined.
  (* tLetIn *)
  Next Obligation. econstructor; cbn; easy. Defined.
  Next Obligation. econstructor; eassumption. Defined.

  (* tApp *)
  Next Obligation. now eapply welltyped_type. Defined.
  Next Obligation.
    econstructor. 2: eassumption.
    eapply type_reduction; eassumption.
  Defined.

  (* tConst *)
  Next Obligation.
    constructor; try assumption.
    symmetry in Heq_anonymous.
    etransitivity. eassumption.
    now rewrite (lookup_env_id _ _ _ Heq_anonymous).
  Defined.

  (* tInd *)
  Next Obligation. econstructor; eassumption. Defined.

  (* tConstruct *)
  Next Obligation. econstructor; try eassumption. now split. Defined.

  (* tCase *)
  Next Obligation. now eapply welltyped_type. Defined.
  Next Obligation.
    econstructor; try eassumption.
    - destruct (ssrbool.elimT (eq_ind_spec ind I)); eassumption.
    - apply beq_nat_true; assumption.
    - symmetry; eassumption.
  Defined.

  (* tProj *)
  Next Obligation. now eapply welltyped_type. Defined.
  Next Obligation.
    eapply type_Proj with (pdecl := (i, t0)).
    - split. eassumption. symmetry; eassumption.
    - cbn. destruct (ssrbool.elimT (eq_ind_spec ind I)); [assumption|].
      eapply type_reduction; eassumption.
    - apply beq_nat_true; assumption.
  Defined.

  (* tFix *)
  Next Obligation. now eapply All_local_env_app_inv. Defined.
  Next Obligation. now eapply All_local_env_app_inv. Defined.

  (* tCoFix *)
  Next Obligation. now eapply All_local_env_app_inv. Defined.
  Next Obligation. now eapply All_local_env_app_inv. Defined.

End Typecheck.

Extraction infer.







(* smlqjs *)


(*   Fixpoint infer (Γ : context) (t : term) : typing_result term := *)
(*     match t with *)
(*     | tRel n => *)
(*       match nth_error Γ n with *)
(*       | Some d => ret (lift0 (S n) d.(decl_type)) *)
(*       | None => raise (UnboundRel n) *)
(*       end *)

(*     | tVar n => raise (UnboundVar n) *)
(*     | tMeta n => raise (UnboundMeta n) *)
(*     | tEvar ev args => raise (UnboundEvar ev) *)

(*     | tSort s => ret (tSort (try_suc s)) *)

(*     | tProd n t b => *)
(*       s1 <- infer infer Γ t ;; *)
(*       s2 <- infer_type infer (Γ ,, vass n t) b ;; *)
(*       ret (tSort (Universe.sort_of_product s1 s2)) *)

(*     | tLambda n t b => *)
(*       infer_type infer Γ t ;; *)
(*       t2 <- infer (Γ ,, vass n t) b ;; *)
(*       ret (tProd n t t2) *)

(*     | tLetIn n b b_ty b' => *)
(*       infer_type infer Γ b_ty ;; *)
(*        infer_cumul infer Γ b b_ty ;; *)
(*        b'_ty <- infer (Γ ,, vdef n b b_ty) b' ;; *)
(*        ret (tLetIn n b b_ty b'_ty) *)

(*     | tApp t a => *)
(*       ty <- infer Γ t ;; *)
(*       pi <- reduce_to_prod (fst Σ) Γ ty ;; *)
(*       let '(a1, b1) := pi in *)
(*       infer_cumul infer Γ a a1;; *)
(*       ret (subst10 a b1) *)

(*     | tConst cst u => *)
(*       tycstrs <- lookup_constant_type_cstrs cst u ;; *)
(*       let '(ty, cstrs) := tycstrs in *)
(*       check_consistent_constraints cstrs;; *)
(*       ret ty *)

(*     | tInd (mkInd ind i) u => *)
(*       tycstrs <- lookup_ind_type_cstrs ind i u;; *)
(*       let '(ty, cstrs) := tycstrs in *)
(*       check_consistent_constraints cstrs;; *)
(*       ret ty *)

(*     | tConstruct (mkInd ind i) k u => *)
(*       tycstrs <- lookup_constructor_type_cstrs ind i k u ;; *)
(*       let '(ty, cstrs) := tycstrs in *)
(*       check_consistent_constraints cstrs;; *)
(*       ret ty *)

(*     | tCase (ind, par) p c brs => *)
(*       ty <- infer Γ c ;; *)
(*       indargs <- reduce_to_ind (fst Σ) Γ ty ;; *)
(*       (** TODO check branches *) *)
(*       let '(ind', u, args) := indargs in *)
(*       if eq_ind ind ind' then *)
(*         ret (mkApps p (List.skipn par args ++ [c])) *)
(*       else *)
(*         let ind1 := tInd ind u in *)
(*         let ind2 := tInd ind' u in *)
(*         raise (NotConvertible Γ ind1 ind2 ind1 ind2) *)

(*     | tProj p c => *)
(*       ty <- infer Γ c ;; *)
(*       indargs <- reduce_to_ind (fst Σ) Γ ty ;; *)
(*       (* FIXME *) *)
(*       ret ty *)

(*     | tFix mfix n => *)
(*       match nth_error mfix n with *)
(*       | Some f => ret f.(dtype) *)
(*       | None => raise (IllFormedFix mfix n) *)
(*       end *)

(*     | tCoFix mfix n => *)
(*       match nth_error mfix n with *)
(*       | Some f => ret f.(dtype) *)
(*       | None => raise (IllFormedFix mfix n) *)
(*       end *)
(*     end. *)

(*   Definition check (Γ : context) (t : term) (ty : term) : typing_result unit := *)
(*     infer Γ ty ;; *)
(*     infer_cumul infer Γ t ty ;; *)
(*     ret (). *)

(*   Definition typechecking (Γ : context) (t ty : term) := *)
(*     match check Γ t ty with *)
(*     | Checked _ => true *)
(*     | TypeError _ => false *)
(*     end. *)

(*   Ltac tc := eauto with typecheck. *)

(*   Arguments bind _ _ _ _ ! _. *)
(*   Open Scope monad. *)

(*   Conjecture cumul_convert_leq : forall Γ t t', *)
(*     Σ ;;; Γ |- t <= t' <~> convert_leq Γ t t' = Checked (). *)

(*   Conjecture cumul_reduce_to_sort : forall Γ t s', *)
(*       Σ ;;; Γ |- t <= tSort s' <~> *)
(*       exists s'', reduce_to_sort (fst Σ) Γ t = Checked s'' *)
(*              /\ check_leq (snd Σ) s'' s' = true. *)

(*   Conjecture cumul_reduce_to_product : forall Γ t na a b, *)
(*       Σ ;;; Γ |- t <= tProd na a b -> *)
(*       exists a' b', *)
(*         reduce_to_prod (fst Σ) Γ t = Checked (a', b') /\ *)
(*         squash (cumul Σ Γ (tProd na a' b') (tProd na a b)). *)

(*   Conjecture cumul_reduce_to_ind : forall Γ t i u args, *)
(*       Σ ;;; Γ |- t <= mkApps (tInd i u) args <~> *)
(*       exists args', *)
(*         reduce_to_ind (fst Σ) Γ t = Checked (i, u, args') /\ *)
(*         squash (cumul Σ Γ (mkApps (tInd i u) args') (mkApps (tInd i u) args)). *)

(*   Lemma lookup_env_id {id decl} : lookup_env Σ id = Some decl -> id = global_decl_ident decl. *)
(*   Proof. *)
(*     destruct Σ. *)
(*     unfold lookup_env. *)
(*     induction g; simpl; intros; try discriminate; trivial. *)
(*     revert H. destruct (ident_eq_spec id (global_decl_ident a)). now intros [= ->]. *)
(*     apply IHg. *)
(*   Qed. *)

(*   Lemma lookup_constant_type_declared cst u decl (isdecl : declared_constant (fst Σ) cst decl) : *)
(*     lookup_constant_type_cstrs cst u = *)
(*     Checked (subst_instance_constr u decl.(cst_type), *)
(*              subst_instance_cstrs u (polymorphic_constraints decl.(cst_universes))). *)
(*   Proof. *)
(*     unfold lookup_constant_type_cstrs, lookup_env. *)
(*     red in isdecl. rewrite isdecl. destruct decl. reflexivity. *)
(*   Qed. *)

(*   Lemma lookup_constant_type_is_declared cst u T : *)
(*     lookup_constant_type_cstrs cst u = Checked T -> *)
(*     { decl | declared_constant (fst Σ) cst decl /\ *)
(*              subst_instance_constr u decl.(cst_type) = fst T }. *)
(*   Proof. *)
(*     unfold lookup_constant_type_cstrs, lookup_env, declared_constant. *)
(*     destruct PCUICTyping.lookup_env eqn:Hlook; try discriminate. *)
(*     destruct g eqn:Hg; intros; try discriminate. destruct c. *)
(*     injection H as eq. subst T. rewrite (lookup_env_id Hlook). simpl. *)
(*     eexists. split; eauto. *)
(*   Qed. *)

(*   Lemma eq_ind_refl i i' : eq_ind i i' = true <-> i = i'. *)
(*   Admitted. *)

(*   Hint Resolve sq. *)

(*   Ltac unsquash := *)
(*     repeat match goal with *)
(*              | [ H : squash _ |- _ ] => destruct H as [H] *)
(*            end. *)

(*   Lemma infer_complete Γ t T : *)
(*     Σ ;;; Γ |- t : T -> exists T', infer Γ t = Checked T' /\ squash (cumul Σ Γ T' T). *)
(*   Proof. *)
(*     induction 1; unfold infer_type, infer_cumul in *; simpl; unfold infer_type, infer_cumul in *; *)
(*       repeat match goal with *)
(*         H : exists T', _ |- _ => destruct H as [? [-> H]] *)
(*       end; simpl; try (eexists; split; [ reflexivity | solve [ tc ] ]); unsquash. *)

(*     - eexists. rewrite e. *)
(*       split; [ reflexivity | tc ]. *)

(*     - eexists. split; [reflexivity | tc]. *)
(*       constructor. simpl. unfold leq_universe. *)
(*       admit. *)

(*     - eexists. *)
(*       apply cumul_reduce_to_sort in IHX1 as [s'' [-> Hs'']]. *)
(*       admit. *)

(*     - apply cumul_reduce_to_sort in IHX1 as [s'' [-> Hs'']]. *)
(*       eexists; intuition eauto. constructor. *)
(*       eapply congr_cumul_prod; tc. *)

(*     - apply cumul_convert_leq in IHX2 as ->; simpl. *)
(*       apply cumul_reduce_to_sort in IHX1 as [s'' [-> Hs'']]. *)
(*       simpl. eexists; split; [reflexivity|]. *)
(*       admit. *)

(*     - admit. *)

(*     - erewrite lookup_constant_type_declared; eauto. *)
(*       eexists ; split; [ try reflexivity | tc ]. *)
(*       simpl. unfold consistent_universe_context_instance in c. *)
(*       destruct cst_universes. *)
(*       -- simpl. reflexivity. *)
(*       -- simpl in *. destruct cst0. simpl in *. *)
(*          destruct c. unfold check_consistent_constraints. rewrite H0. reflexivity. *)
(*       -- simpl in *. destruct ctx as [[inst csts] variance]. simpl in *. *)
(*          destruct c. unfold check_consistent_constraints. rewrite H0. reflexivity. *)

(*     - admit. *)
(*     - admit. *)

(*     - (* destruct indpar. *) *)
(*       apply cumul_reduce_to_ind in IHX2 as [args' [-> Hcumul]]. *)
(*       simpl in *. rewrite (proj2 (eq_ind_refl ind ind) eq_refl). *)
(*       eexists ; split; [ reflexivity | tc ]. *)
(*       admit. *)

(*     - admit. *)

(*     - eexists. rewrite e. *)
(*       split; [ reflexivity | tc ]. *)

(*     - eexists. rewrite e. *)
(*       split; [ reflexivity | tc ]. *)

(*     - eexists. *)
(*       split; [ reflexivity | tc ]. constructor. *)
(*       eapply cumul_trans; eauto. *)
(*   Admitted. *)

(*   Ltac infers := *)
(*     repeat *)
(*       match goal with *)
(*       | |- context [infer ?Γ ?t] => *)
(*         destruct (infer Γ t) eqn:?; [ simpl | simpl; intro; discriminate ] *)
(*       | |- context [infer_type ?Γ ?t] => *)
(*         destruct (infer_type Γ t) eqn:?; [ simpl | simpl; intro; discriminate ] *)
(*       | |- context [infer_cumul ?Γ ?t ?t2] => *)
(*         destruct (infer_cumul Γ t t2) eqn:?; [ simpl | simpl; intro; discriminate ] *)
(*       | |- context [convert_leq ?Γ ?t ?t2] => *)
(*         destruct (convert_leq Γ t t2) eqn:?; [ simpl | simpl; intro; discriminate ] *)
(*       end; try intros [= <-]. *)

(*   Lemma leq_universe_refl `{config.checker_flags} x : check_leq (snd Σ) x x = true. (* FIXME condition on φ? *) *)
(*   Proof. induction x. unfold check_leq. cbn. auto with bool. unfold check_leq. simpl. Admitted. *)
(*   Hint Resolve leq_universe_refl : typecheck. *)
(*   Lemma infer_type_correct Γ t x : *)
(*     (forall (Γ : context) (T : term), infer Γ t = Checked T -> Σ ;;; Γ |- t : T) -> *)
(*     infer_type infer Γ t = Checked x -> *)
(*     Σ ;;; Γ |- t : tSort x. *)
(*   Proof. *)
(*     intros IH H. *)
(*     unfold infer_type in H. *)
(*     revert H; infers. *)
(*     specialize (IH _ _ Heqt0). *)
(*     intros. *)
(*     eapply type_Conv. apply IH. *)
(*     admit. apply cumul_reduce_to_sort. exists x. split; tc. *)
(*   Admitted. *)


(*   Lemma infer_cumul_correct Γ t u x x' : *)
(*     (forall (Γ : context) (T : term), infer Γ u = Checked T -> Σ ;;; Γ |- u : T) -> *)
(*     (forall (Γ : context) (T : term), infer Γ t = Checked T -> Σ ;;; Γ |- t : T) -> *)
(*     infer_type infer Γ u = Checked x' -> *)
(*     infer_cumul infer Γ t u = Checked x -> *)
(*     Σ ;;; Γ |- t : u. *)
(*   Proof. *)
(*     intros IH IH' H H'. *)
(*     unfold infer_cumul in H'. *)
(*     revert H'; infers. *)
(*     specialize (IH' _ _ Heqt0). *)
(*     intros. *)
(*     eapply type_Conv. apply IH'. *)
(*     apply infer_type_correct; eauto. *)
(*     destruct a0. now apply cumul_convert_leq. *)
(*   Qed. *)

(*   Ltac infco := eauto using infer_cumul_correct, infer_type_correct. *)

(*   (* Axiom cheat : forall A, A. *) *)
(*   (* Ltac admit := apply cheat. *) *)

(*   Lemma infer_correct Γ t T : wf_local Σ Γ -> *)
(*     infer Γ t = Checked T -> Σ ;;; Γ |- t : T. *)
(*   Proof. *)
(*     induction t in Γ, T |- * ; simpl; intros; try discriminate; *)
(*       revert H; infers; try solve [econstructor; infco]. *)

(*     - destruct nth_error eqn:Heq; try discriminate. *)
(*       intros [= <-]. constructor; auto. *)

(*     - admit. *)
(*     - admit. *)

(*     - admit. *)
(*     (*  intros. *) *)
(*       (* destruct (lookup_constant_type) eqn:?. simpl in *. *) *)
(*       (* apply (lookup_constant_type_is_declared k u) in Heqt. *) *)
(*       (* destruct Heqt as [decl [Hdecl Heq]]. *) *)
(*       (* destruct a eqn:eqa. simpl in *. *) *)
(*       (* destruct check_consistent_constraints eqn:cons. *) *)

(*       (* simpl in *. injection H as ->. rewrite <- Heq. constructor. auto. *) *)
(*       (* red in Hdecl. *) *)
(*       (* unfold consistent_universe_context_instance. *) *)
(*       (* unfold check_consistent_constraints in cons. *) *)
(*       (* unfold check_constraints in cons. *) *)
(*       (* destruct decl. simpl in *. *) *)

(*       (* destruct decl; simpl in *. destruct cst_universes; simpl in *. auto. *) *)
(*       (* destruct cst. simpl. unfold check_consistent_constraints in cons. split; auto. *) *)
(*       (* unfold lookup_constant_type in Heqt. *) *)

(*       (* pose (lookup_constant_type_is_declared k u). _ _ _ H) as [decl [Hdecl <-]]. *) *)
(*       (* constructor. auto. *) *)

(*     - (* Ind *) admit. *)

(*     - (* Construct *) admit. *)

(*     - (* Case *) *)
(*       (* destruct p. *) *)
(*       (* infers. *) *)
(*       (* destruct reduce_to_ind eqn:?; try discriminate. simpl. *) *)
(*       (* destruct a0 as [[ind' u] args]. *) *)
(*       (* destruct eq_ind eqn:?; try discriminate. *) *)
(*       (* intros [= <-]. *) *)
(*       admit. *)
(*       (* eapply type_Case. simpl in *. *) *)
(*       (* eapply type_Conv. eauto. *) *)
(*       (* admit. *) *)
(*       (* rewrite cumul_reduce_to_ind. *) *)
(*       (* exists args. split; auto. *) *)
(*       (* rewrite Heqt0. repeat f_equal. apply eq_ind_refl in Heqb. congruence. *) *)
(*       (* tc. *) *)

(*     - (* Proj *) admit. *)
(*     - admit. *)
(*     - admit. *)
(*     - admit. *)
(*     - admit. *)

(*     - destruct nth_error eqn:?; intros [= <-]. *)
(*       constructor; auto. admit. admit. *)

(*   Admitted. *)

(* End Typecheck2. *)

(* Extract Constant infer_type_correct => "(fun f sigma ctx t x -> assert false)". *)
(* Extract Constant infer_correct => "(fun f sigma ctx t ty -> assert false)". *)

(* Definition default_fuel : Fuel := 2 ^ 14. *)

(* Fixpoint fresh id env : bool := *)
(*   match env with *)
(*   | nil => true *)
(*   | cons g env => negb (eq_constant (global_decl_ident g) id) && fresh id env *)
(*   end. *)

(* Section Checker. *)

(*   Context `{cf : checker_flags}. *)
(*   Context `{F:Fuel}. *)

(*   Inductive env_error := *)
(*   | IllFormedDecl (e : string) (e : type_error) *)
(*   | AlreadyDeclared (id : string). *)

(*   Inductive EnvCheck (A : Type) := *)
(*   | CorrectDecl (a : A) *)
(*   | EnvError (e : env_error). *)
(*   Global Arguments EnvError {A} e. *)
(*   Global Arguments CorrectDecl {A} a. *)

(*   Instance envcheck_monad : Monad EnvCheck := *)
(*     {| ret A a := CorrectDecl a ; *)
(*        bind A B m f := *)
(*          match m with *)
(*          | CorrectDecl a => f a *)
(*          | EnvError e => EnvError e *)
(*          end *)
(*     |}. *)

(*   Definition wrap_error {A} (id : string) (check : typing_result A) : EnvCheck A := *)
(*     match check with *)
(*     | Checked a => CorrectDecl a *)
(*     | TypeError e => EnvError (IllFormedDecl id e) *)
(*     end. *)

(*   Definition check_wf_type id Σ t := *)
(*     wrap_error id (infer_type Σ (infer Σ) [] t) ;; ret (). *)

(*   Definition check_wf_judgement id Σ t ty := *)
(*     wrap_error id (check Σ [] t ty) ;; ret (). *)

(*   Definition infer_term Σ t := *)
(*     wrap_error "" (infer Σ [] t). *)

(*   Definition check_wf_decl Σ (g : global_decl) : EnvCheck () := *)
(*     match g with *)
(*     | ConstantDecl id cst => *)
(*       match cst.(cst_body) with *)
(*       | Some term => check_wf_judgement id Σ term cst.(cst_type) *)
(*       | None => check_wf_type id Σ cst.(cst_type) *)
(*       end *)
(*     | InductiveDecl id inds => *)
(*       List.fold_left (fun acc body => *)
(*                         acc ;; check_wf_type body.(ind_name) Σ body.(ind_type)) *)
(*                      inds.(ind_bodies) (ret ()) *)
(*     end. *)

(*   Fixpoint check_fresh id env : EnvCheck () := *)
(*     match env with *)
(*     | [] => ret () *)
(*     | g :: env => *)
(*       check_fresh id env;; *)
(*       if eq_constant id (global_decl_ident g) then *)
(*         EnvError (AlreadyDeclared id) *)
(*       else ret () *)
(*     end. *)

(*   Fixpoint check_wf_declarations (φ : uGraph.t) (g : global_declarations) := *)
(*     match g with *)
(*     | [] => ret () *)
(*     | g :: env => *)
(*       check_wf_declarations φ env ;; *)
(*       check_wf_decl (env, φ) g ;; *)
(*       check_fresh (global_decl_ident g) env *)
(*     end. *)

(*   Definition check_wf_env (Σ : global_context) := *)
(*     if negb (no_universe_inconsistency (snd Σ)) then *)
(*       EnvError (AlreadyDeclared "univ inconsistency") (* todo better error *) *)
(*     else check_wf_declarations (snd Σ) (fst Σ). *)

(*   Definition typecheck_program (p : program) : EnvCheck term := *)
(*     let Σ := reconstruct_global_context (fst p) in *)
(*     check_wf_env Σ ;; infer_term Σ (snd p). *)

(* End Checker. *)
