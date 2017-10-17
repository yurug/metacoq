From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Template Ast Induction LiftSubst Typing.

Set Asymmetric Patterns.
Generalizable Variables Σ Γ t T.

Lemma length_app_context Γ Γ' : #|Γ ,,, Γ'| = #|Γ| + #|Γ'|.
Proof.
  unfold app_context. rewrite app_length. omega.
Qed.

Definition map_decl (f : term -> term) (d : context_decl) : context_decl :=
  {| decl_name := d.(decl_name);
     decl_body := option_map f d.(decl_body);
     decl_type := f d.(decl_type) |}.

Definition lift_decl n k (d : context_decl) := map_decl (lift n k) d.

Definition lift_context_rec n k (Γ : context) : nat * context :=
  List.fold_right (fun decl '(k, Γ) => (S k, lift_decl n k decl :: Γ)) (k, []) Γ.

Definition lift_context n k Γ := snd (lift_context_rec n k Γ).

Lemma lift0_context k Γ : lift_context 0 k Γ = Γ.
Proof.
  unfold lift_context; induction Γ; simpl; trivial.
  simpl. destruct lift_context_rec. simpl in *.
  unfold lift_decl, map_decl. destruct a. simpl. rewrite IHΓ; f_equal.
  rewrite lift_rec0. now destruct decl_body; simpl; rewrite ?lift_rec0.
Qed.
  
Lemma lift_context_rec_fst n k Γ :
  fst (lift_context_rec n k Γ) = #|Γ| + k.
Proof.
  induction Γ; simpl; auto.
  destruct lift_context_rec; simpl in *.
  congruence.
Qed.
Hint Rewrite lift_context_rec_fst : lift.

Lemma lift_context_len n k Γ : #|lift_context n k Γ| = #|Γ|.
Proof.
  unfold lift_context; induction Γ; simpl; trivial.
  destruct lift_context_rec. simpl in *. auto with arith.
Qed.
Hint Rewrite lift_context_len : lift.

Lemma lift_context_snoc n k Γ d : lift_context n k (Γ ,, d) = lift_context n k Γ ,, lift_decl n (#|Γ| + k) d.
Proof.
  unfold lift_context.
  simpl.
  pose proof (lift_context_rec_fst n k Γ).
  revert H. destruct lift_context_rec. simpl.
  now intros ->.
Qed.
Hint Rewrite lift_context_snoc : lift.

Lemma some_inj {A} {x y : A} : Some x = Some y -> x = y.
Proof.
  now intros [=].
Qed.

Lemma nth_error_app_ge v Γ Γ' : #|Γ'| <= v -> nth_error (Γ ,,, Γ') v = nth_error Γ (v - #|Γ'|).
Proof.
  revert v; induction Γ'; simpl; intros.

  now rewrite Nat.sub_0_r.
  destruct v. omega.
  simpl. rewrite IHΓ'; easy.
Qed.

Lemma nth_error_app_lt v Γ Γ' : v < #|Γ'| -> nth_error (Γ ,,, Γ') v = nth_error Γ' v.
Proof.
  revert v; induction Γ'; simpl; intros. easy.

  destruct v; trivial.
  simpl. rewrite IHΓ'; easy.
Qed.

Lemma weaken_safe_nth_ge Γ Γ' v (isdecl : v < #|Γ ,,, Γ'|) Γ'' : #|Γ'| <= v ->
  { isdecl' : _ &
  safe_nth (Γ ,,, Γ') (exist (fun n0 : nat => n0 < #|Γ ,,, Γ'|) v isdecl) =
  safe_nth (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (exist _ (#|Γ''| + v) isdecl') }.
Proof.
  simpl.
  assert(#|Γ''| + v < #|Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'|).
  rewrite !length_app_context in *. autorewrite with lift. omega.
  exists H.
  apply some_inj; rewrite <- !nth_error_safe_nth.
  rewrite nth_error_app_ge; try easy.
  rewrite (nth_error_app_ge (_ + v)); rewrite ?lift_context_len; try easy.
  rewrite nth_error_app_ge; rewrite ?lift_context_len; try easy.
Qed.

Lemma weaken_safe_nth_lt Γ Γ' v (isdecl : v < #|Γ ,,, Γ'|) Γ'' : v < #|Γ'| ->
  { isdecl' : _ &
  safe_nth (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (exist _ v isdecl') =
  lift_decl #|Γ''| (#|Γ'| - S v)
       (safe_nth (Γ ,,, Γ') (exist (fun n0 : nat => n0 < #|Γ ,,, Γ'|) v isdecl)) }.
Proof.
  simpl. intros Hv.
  assert(v < #|Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'|).
  rewrite !length_app_context in *. autorewrite with lift. omega.
  exists H.
  apply some_inj. rewrite <- !nth_error_safe_nth.
  rewrite nth_error_app_lt. 2:rewrite !length_app_context in H; autorewrite with lift; omega.
  remember (safe_nth (Γ ,,, Γ') (exist _ v isdecl)) as nth.
  apply (f_equal Some) in Heqnth. rewrite <- nth_error_safe_nth in Heqnth.
  rewrite nth_error_app_lt in Heqnth; try easy.
  clear isdecl H Γ.
  revert Γ'' v Hv nth Heqnth.
  induction Γ'; intros.
  - easy.
  - simpl. destruct v.
    + simpl. unfold lift_context. simpl.
      destruct lift_context_rec eqn:Heq.
      pose proof (lift_context_rec_fst #|Γ''| 0 Γ'). rewrite Heq in H. simpl in H. subst n.
      simpl. rewrite Nat.add_0_r, Nat.sub_0_r.
      simpl in *. now injection Heqnth as ->.
    + simpl.
      unfold lift_context. simpl.
      destruct lift_context_rec eqn:Heq.
      pose proof (lift_context_rec_fst #|Γ''| 0 Γ'). rewrite Heq in H. simpl in H. subst n.
      simpl in *.
      assert (v < #|Γ'|) by easy.
      specialize (IHΓ' Γ'' v  H nth Heqnth).
      rewrite <- IHΓ'.
      f_equal. unfold lift_context. rewrite Heq. reflexivity.
Qed.  

Lemma typecheck_closed : env_prop (fun Σ Γ t T =>
                                     type_local_env Σ Γ ->
                                     closedn #|Γ| t && closedn #|Γ| T = true).
Proof.
  apply typing_ind_env; intros; simpl; rewrite ?andb_true_iff in *; try solve [intuition auto].
  - elim (Nat.ltb_spec n #|Γ|); intuition.
    admit (* Need induction with IHs for environments *).
  - intuition auto.
    + eapply H2. constructor; auto.
      red. now exists s1. 
  - intuition; eapply H2; constructor; auto.
    now exists s1. now exists s1. 
  - intuition; try eapply H4; try constructor; auto.
  - (* typing spine ind *) admit.
  - admit. (* easy now *)
  - admit.
  - admit.
  - specialize (H5 H9).
    intuition auto. admit. admit. 
  - (* proj *) admit.
  - admit.
  - admit.
Admitted.

Inductive BoolSpecSet (P Q : Prop) : bool -> Set :=
    BoolSpecT : P -> BoolSpecSet P Q true | BoolSpecF : Q -> BoolSpecSet P Q false.

Lemma leb_spec_Set : forall x y : nat, BoolSpecSet (x <= y) (y < x) (x <=? y).
Proof.
  intros. 
  destruct (Nat.leb_spec0 x y).
  now constructor.
  constructor. now auto with arith.
Qed.

Lemma typing_ind_env :
  forall (P : global_context -> context -> term -> term -> Set),
    (forall Σ (wfΣ : wf Σ) (Γ : context) (n : nat) (isdecl : n < #|Γ|),
        P Σ Γ (tRel n)
          (lift0 (S n) (decl_type (safe_nth Γ (exist (fun n0 : nat => n0 < #|Γ|) n isdecl))))) ->
    (forall Σ (wfΣ : wf Σ) (Γ : context) (s : sort), P Σ Γ (tSort s) (tSort (succ_sort s))) ->
    (forall Σ (wfΣ : wf Σ) (Γ : context) (c : term) (k : cast_kind) (t : term) (s : sort),
        Σ;;; Γ |-- t : tSort s -> P Σ Γ t (tSort s) -> Σ;;; Γ |-- c : t -> P Σ Γ c t -> P Σ Γ (tCast c k t) t) ->
    (forall Σ (wfΣ : wf Σ) (Γ : context) (n : name) (t b : term) (s1 s2 : sort),
        Σ;;; Γ |-- t : tSort s1 ->
        P Σ Γ t (tSort s1) ->
        Σ;;; Γ,, vass n t |-- b : tSort s2 ->
        P Σ (Γ,, vass n t) b (tSort s2) -> P Σ Γ (tProd n t b) (tSort (max_sort s1 s2))) ->
    (forall Σ (wfΣ : wf Σ) (Γ : context) (n n' : name) (t b : term) (s1 : sort) (bty : term),
        Σ;;; Γ |-- t : tSort s1 ->
        P Σ Γ t (tSort s1) ->
        Σ;;; Γ,, vass n t |-- b : bty -> P Σ (Γ,, vass n t) b bty -> P Σ Γ (tLambda n t b) (tProd n' t bty)) ->
    (forall Σ (wfΣ : wf Σ) (Γ : context) (n : name) (b b_ty b' : term) (s1 : sort) (b'_ty : term),
        Σ;;; Γ |-- b_ty : tSort s1 ->
        P Σ Γ b_ty (tSort s1) ->
        Σ;;; Γ |-- b : b_ty ->
        P Σ Γ b b_ty ->
        Σ;;; Γ,, vdef n b b_ty |-- b' : b'_ty ->
        P Σ (Γ,, vdef n b b_ty) b' b'_ty -> P Σ Γ (tLetIn n b b_ty b') (tLetIn n b b_ty b'_ty)) ->
    (forall Σ (wfΣ : wf Σ) (Γ : context) (t : term) (l : list term) (t_ty t' : term),
        Σ;;; Γ |-- t : t_ty -> P Σ Γ t t_ty -> typing_spine Σ Γ t_ty l t' -> P Σ Γ (tApp t l) t') ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (cst : ident) (decl : constant_decl),
        declared_constant Σ cst decl ->
        Forall_decls_typing (fun Σ t ty => P Σ [] t ty) Σ ->
        P Σ Γ (tConst cst) (cst_type decl)) ->

        (forall Σ (wfΣ : wf Σ) (Γ : context) (ind : inductive) (decl : inductive_body),
        declared_inductive Σ ind decl -> P Σ Γ (tInd ind) (ind_type decl)) ->
       (forall Σ (wfΣ : wf Σ) (Γ : context) (ind : inductive) (i : nat) (decl : ident * term * nat)
          (isdecl : declared_constructor Σ (ind, i) decl),
        P Σ Γ (tConstruct ind i) (type_of_constructor Σ (ind, i) decl isdecl)) ->
       (forall Σ (wfΣ : wf Σ) (Γ : context) (ind : inductive) (npar : nat) (p c : term) (brs : list (nat * term))
          (args : list term) (decl : minductive_decl),
        declared_minductive Σ (inductive_mind ind) decl ->
        forall decl' : inductive_body,
        declared_inductive Σ ind decl' ->
        ind_npars decl = npar ->
        let pars := firstn npar args in
        forall (pty : term) (s : sort) (btys : list (nat * term)),
        types_of_case ind pars p decl' = Some (pty, s, btys) ->
        Exists (fun sf : sort_family => allowed_elim s sf = true) (ind_kelim decl') ->
        Σ;;; Γ |-- p : pty ->
        P Σ Γ p pty ->
        Σ;;; Γ |-- c : mktApp (tInd ind) args ->
        P Σ Γ c (mktApp (tInd ind) args) ->
        Forall2 (fun x y : nat * term => fst x = fst y /\ squash (Σ;;; Γ |-- snd x : snd y)) brs btys ->
        P Σ Γ (tCase (ind, npar) p c brs) (tApp p (skipn npar args ++ [c]))) ->
       (forall Σ (wfΣ : wf Σ) (Γ : context) (p : projection) (c : term) (decl : ident * term),
        declared_projection Σ p decl ->
        forall args : list term,
        Σ;;; Γ |-- c : mktApp (tInd (fst (fst p))) args ->
        P Σ Γ c (mktApp (tInd (fst (fst p))) args) ->
        let ty := snd decl in P Σ Γ (tProj p c) (substl (c :: rev args) ty)) ->
       (forall Σ (wfΣ : wf Σ) (Γ : context) (mfix : list (def term)) (n : nat) (isdecl : n < #|mfix|),
        let ty := dtype (safe_nth mfix (exist (fun n0 : nat => n0 < #|mfix|) n isdecl)) in
        P Σ Γ (tFix mfix n) ty) ->
       (forall Σ (wfΣ : wf Σ) (Γ : context) (mfix : list (def term)) (n : nat) (isdecl : n < #|mfix|),
        let ty := dtype (safe_nth mfix (exist (fun n0 : nat => n0 < #|mfix|) n isdecl)) in
        P Σ Γ (tCoFix mfix n) ty) ->
       (forall Σ (wfΣ : wf Σ) (Γ : context) (t A B : term) (s : sort),
        Σ;;; Γ |-- t : A ->
                       P Σ Γ t A -> Σ;;; Γ |-- B : tSort s -> P Σ Γ B (tSort s) -> Σ;;; Γ |-- A <= B -> P Σ Γ t B) ->

       forall Σ (ψfΣ : wf Σ) Γ t T, Σ;;; Γ |-- t : T -> P Σ Γ t T.
Proof.
  intros.
  eapply typing_ind_env; eauto.
Qed.
  

Lemma weakening_rec Σ Γ Γ' Γ'' :
  type_global_env Σ -> type_local_env Σ (Γ ,,, Γ') ->
  type_local_env Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') ->
  `(Σ ;;; Γ ,,, Γ' |-- t : T ->
    Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |--
    lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'| T).
Proof.
  intros HΣ HΓΓ' HΓ'' * H. revert Γ'' HΓ''.
  do_depind ltac:(fun hyp => elim hyp using typing_ind_env; clear hyp; clear) H;
    try intros Γ'' HΓ''; simpl in *; try solve [econstructor; eauto].

  - elim (leb_spec_Set); intros Hn.
    + destruct (weaken_safe_nth_ge _ _ _ isdecl Γ'' Hn) as [isdecl' ->].
      rewrite simpl_lift_rec; try omega. rewrite Nat.add_succ_r.
      constructor. 
    + destruct (weaken_safe_nth_lt _ _ _ isdecl Γ'' Hn) as [isdecl' H'].
      apply (f_equal decl_type) in H'.
      unfold lift_decl in H'. simpl in H'.
      assert (forall t, lift0 (S n) (lift #|Γ''| (#|Γ'| - S n) t) = lift #|Γ''| #|Γ'| (lift0 (S n) t)).
      intros. assert (#|Γ'| = S n + (#|Γ'| - S n)) by easy.
      rewrite H at 2.
      rewrite <- permute_lift_rec; try easy.
      rewrite <- H. rewrite <- H'. do 2 constructor.

  - econstructor; auto.
    simpl.
    specialize (x1 Γ Γ' wfΣ HΓΓ' eq_refl).
    specialize (x Γ (Γ' ,, vass n t) wfΣ).
    forward x. constructor; simpl; auto. red. now exists s1.
    specialize (x eq_refl Γ'').
    forward x. rewrite lift_context_snoc. simpl. constructor. simpl; auto.
    exists s1. simpl. rewrite Nat.add_0_r. eapply x1; auto. 
    rewrite lift_context_snoc, plus_0_r in x.
    eapply x.

  - econstructor; auto.
    simpl.
    specialize (x1 Γ Γ' wfΣ HΓΓ' eq_refl).
    specialize (x Γ (Γ' ,, vass n t) wfΣ).
    forward x. constructor; simpl; auto. red. now exists s1.
    specialize (x eq_refl Γ'').
    forward x. rewrite lift_context_snoc. simpl. constructor. simpl; auto.
    exists s1. simpl. rewrite Nat.add_0_r. eapply x1; auto. 
    rewrite lift_context_snoc, plus_0_r in x.
    eapply x.

  - econstructor; auto.
    simpl.
    specialize (x1 Γ Γ' wfΣ HΓΓ' eq_refl).
    specialize (x Γ (Γ' ,, vdef n b b_ty) wfΣ).
    forward x. constructor; simpl; auto. 
    specialize (x eq_refl Γ'').
    rewrite lift_context_snoc, plus_0_r in x.
    forward x. simpl. constructor. simpl; auto.
    red. simpl. now eapply (x3 Γ Γ' wfΣ HΓΓ' eq_refl). 
    eapply x. 

  - econstructor; auto.
    simpl.
    admit.

  - red in x0.
    Lemma Forall_decls_typing Σ (wfΣ : wf Σ) P cst decl : Forall_decls_typing P Σ -> lookup_env Σ cst = Some decl ->
      { Σ' : _ & (Forall_decls_typing P Σ' *
                  on_decl_typing (fun t T => P Σ' t T) decl)%type }.
    Proof.
      induction 1; intros [=].
      destruct ident_eq in *. injection H1 as ->.
      eexists. split; eauto. revert o. inversion wfΣ. subst d Σ0.
      revert H4.
      destruct decl; simpl. unfold type_constant_decl. destruct cst_body. auto.
      unfold isType. intros [s Hs]. intros. destruct o.  exists x.
      inversion wfΣ. subst. red in H4. red in H4.
      red in o.
      

    
  - admit.
  - admit.

  - admit.
  - admit.
  - admit.
  - (* Conv *)
    admit.
Admitted.

Lemma type_local_env_app Σ (Γ Γ' : context) : type_local_env Σ (Γ ,,, Γ') -> type_local_env Σ Γ.
Admitted.

Lemma weakening Σ Γ Γ' :
  type_global_env Σ -> type_local_env Σ (Γ ,,, Γ') ->
  `(Σ ;;; Γ |-- t : T ->
    Σ ;;; Γ ,,, Γ' |-- lift0 #|Γ'| t : lift0 #|Γ'| T).
Proof.
  intros HΣ HΓΓ' * H.
  pose (weakening_rec Σ Γ [] Γ').
  forward t0; eauto.
  forward t0; eauto. now eapply type_local_env_app in HΓΓ'. 
Qed.

Lemma substitution Σ Γ n u U :
  type_global_env Σ -> type_local_env Σ Γ ->
  `(Σ ;;; Γ ,, vass n U |-- t : T -> Σ ;;; Γ |-- u : U ->
    Σ ;;; Γ |-- t {0 := u} : T {0 := u}).
Proof.
  intros HΣ HΓ * Ht Hu.
Admitted.
