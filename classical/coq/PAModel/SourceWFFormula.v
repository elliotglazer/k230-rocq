(** The well-founded-set domain in the current variable-only source syntax.
    Its definition uses neither Foundation nor any Skolem function symbols. *)
From PAModel Require Import SetFormulaCodes.
From Undecidability.FOL Require Import Syntax.Facts Deduction.FullNDFacts Sets.minZF.
From Undecidability Require Import Shared.ListAutomation.
From Stdlib Require Import Lia Lists.List.
Import ListAutomationNotations ListAutomationHints.

Open Scope minZFsyn.
Set Implicit Arguments.
#[local] Hint Constructors prv : core.
#[local] Instance wf_pc : peirce := class.

Definition wf_subset (x y : sf_term) : sf_form := ∀ ($0 ∈' x`[↑] → $0 ∈' y`[↑]).
Definition wf_transitive (x : sf_term) : sf_form := ∀ ($0 ∈' x`[↑] → wf_subset $0 x`[↑]).
Definition wf_nonempty (s : sf_term) : sf_form := ∃ ($0 ∈' s`[↑]).
Definition wf_minel (m s : sf_term) : sf_form := m ∈' s ∧ ∀ ($0 ∈' m`[↑] → ¬ ($0 ∈' s`[↑])).
Definition wf_minimal (s : sf_term) : sf_form := ∃ wf_minel $0 s`[↑].
Definition wf_wellf (t : sf_term) : sf_form := ∀ (wf_subset $0 t`[↑] → wf_nonempty $0 → wf_minimal $0).
Definition wf_tw (t : sf_term) : sf_form := wf_transitive t ∧ wf_wellf t.
Definition wf_class (x : sf_term) : sf_form := ∃ (wf_tw $0 ∧ x`[↑] ∈' $0).
Definition wf_domain : sf_form := wf_class $0.

Arguments wf_subset : simpl never.
Arguments wf_transitive : simpl never.
Arguments wf_nonempty : simpl never.
Arguments wf_minel : simpl never.
Arguments wf_minimal : simpl never.
Arguments wf_wellf : simpl never.
Arguments wf_tw : simpl never.
Arguments wf_class : simpl never.
Arguments wf_domain : simpl never.

Lemma wf_subset_subst x y sigma :
  (wf_subset x y)[sigma] = wf_subset x`[sigma] y`[sigma].
Proof. unfold wf_subset. cbn. now rewrite !up_term. Qed.
Lemma wf_transitive_subst x sigma :
  (wf_transitive x)[sigma] = wf_transitive x`[sigma].
Proof. unfold wf_transitive. cbn. rewrite wf_subset_subst. cbn. now rewrite up_term. Qed.
Lemma wf_nonempty_subst x sigma : (wf_nonempty x)[sigma] = wf_nonempty x`[sigma].
Proof. unfold wf_nonempty. cbn. now rewrite up_term. Qed.
Lemma wf_minel_subst x y sigma : (wf_minel x y)[sigma] = wf_minel x`[sigma] y`[sigma].
Proof. unfold wf_minel. cbn. now rewrite !up_term. Qed.
Lemma wf_minimal_subst x sigma : (wf_minimal x)[sigma] = wf_minimal x`[sigma].
Proof. unfold wf_minimal. cbn. rewrite wf_minel_subst. cbn. now rewrite up_term. Qed.
Lemma wf_wellf_subst x sigma : (wf_wellf x)[sigma] = wf_wellf x`[sigma].
Proof.
  unfold wf_wellf. cbn. rewrite wf_subset_subst,wf_nonempty_subst,wf_minimal_subst.
  cbn. now rewrite up_term.
Qed.
Lemma wf_tw_subst x sigma : (wf_tw x)[sigma] = wf_tw x`[sigma].
Proof. unfold wf_tw. cbn. now rewrite wf_transitive_subst,wf_wellf_subst. Qed.
Lemma wf_class_subst x sigma : (wf_class x)[sigma] = wf_class x`[sigma].
Proof. unfold wf_class. cbn. rewrite wf_tw_subst. cbn. now rewrite up_term. Qed.
Lemma wf_domain_up sigma : wf_domain[up sigma] = wf_domain.
Proof. unfold wf_domain. now rewrite wf_class_subst. Qed.
Lemma wf_domain_inst t : wf_domain[t..] = wf_class t.
Proof. unfold wf_domain. now rewrite wf_class_subst. Qed.

#[export] Hint Rewrite wf_subset_subst wf_transitive_subst wf_nonempty_subst
  wf_minel_subst wf_minimal_subst wf_wellf_subst wf_tw_subst wf_class_subst
  wf_domain_up wf_domain_inst : wf_source_subst.
Ltac wf_simp := cbn; autorewrite with wf_source_subst; cbn; subsimpl.
Ltac wf_simp_in H := cbn in H; autorewrite with wf_source_subst in H; cbn in H; subsimpl_in H.

Lemma wf_source_subset_intro T x y :
  (forall z,(z ∈' x :: T) ⊢ z ∈' y) -> T ⊢ wf_subset x y.
Proof. intros H. unfold wf_subset. apply AllI_named. intros z. wf_simp. apply II,H. Qed.
Lemma wf_source_subset_elim T x y z :
  T ⊢ wf_subset x y -> T ⊢ z ∈' x -> T ⊢ z ∈' y.
Proof.
  intros H1 H2. unfold wf_subset in H1. apply (AllE z) in H1. wf_simp_in H1.
  eapply IE; eassumption.
Qed.
Lemma wf_source_transitive_elim T x y z :
  T ⊢ wf_transitive x -> T ⊢ y ∈' x -> T ⊢ z ∈' y -> T ⊢ z ∈' x.
Proof.
  intros H1 H2 H3. unfold wf_transitive in H1. apply (AllE y) in H1. wf_simp_in H1.
  eapply wf_source_subset_elim;[eapply IE;eassumption|exact H3].
Qed.
Lemma wf_source_nonempty_intro T s w : T ⊢ w ∈' s -> T ⊢ wf_nonempty s.
Proof. intro H. unfold wf_nonempty. apply (ExI w). wf_simp. exact H. Qed.
Lemma wf_source_minel_member T m s : T ⊢ wf_minel m s -> T ⊢ m ∈' s.
Proof. intro H. unfold wf_minel in H. eapply CE1,H. Qed.
Lemma wf_source_minel_disjoint T m s z :
  T ⊢ wf_minel m s -> T ⊢ z ∈' m -> T ⊢ z ∈' s -> T ⊢ ⊥.
Proof.
  intros H1 H2 H3. unfold wf_minel in H1. apply CE2,(AllE z) in H1. wf_simp_in H1.
  eapply IE;[eapply IE|];eassumption.
Qed.
Lemma wf_source_minimal_elim T s phi :
  T ⊢ wf_minimal s -> (forall m,(wf_minel m s :: T) ⊢ phi) -> T ⊢ phi.
Proof. intros H1 H2. unfold wf_minimal in H1. apply (ExE_named H1). intros m. wf_simp. apply H2. Qed.
Lemma wf_source_wellf_elim T t s w :
  T ⊢ wf_wellf t -> T ⊢ wf_subset s t -> T ⊢ w ∈' s -> T ⊢ wf_minimal s.
Proof.
  intros H1 H2 H3. unfold wf_wellf in H1. apply (AllE s) in H1. wf_simp_in H1.
  eapply IE;[eapply IE|];[exact H1|exact H2|eapply wf_source_nonempty_intro,H3].
Qed.
Lemma wf_source_tw_transitive T t : T ⊢ wf_tw t -> T ⊢ wf_transitive t.
Proof. intro H. unfold wf_tw in H. eapply CE1,H. Qed.
Lemma wf_source_tw_wellf T t : T ⊢ wf_tw t -> T ⊢ wf_wellf t.
Proof. intro H. unfold wf_tw in H. eapply CE2,H. Qed.
Lemma wf_source_class_intro T x t : T ⊢ wf_tw t -> T ⊢ x ∈' t -> T ⊢ wf_class x.
Proof. intros H1 H2. unfold wf_class. apply (ExI t). wf_simp. now apply CI. Qed.
Lemma wf_source_conjunction_split (T:list sf_form) (phi psi chi:sf_form) :
  (phi :: psi :: T) ⊢ chi -> (phi ∧ psi :: T) ⊢ chi.
Proof.
  intro H. apply (prv_cut H). intros a [<-|[<-|Ha]].
  - eapply CE1,Ctx. auto.
  - eapply CE2,Ctx. auto.
  - apply Ctx. auto.
Qed.
Lemma wf_source_class_elim T x phi :
  T ⊢ wf_class x -> (forall t,(wf_tw t :: x ∈' t :: T) ⊢ phi) -> T ⊢ phi.
Proof.
  intros H1 H2. unfold wf_class in H1. apply (ExE_named H1). intros t. wf_simp.
  apply wf_source_conjunction_split,H2.
Qed.
Lemma wf_source_member T x y :
  T ⊢ wf_class x -> T ⊢ y ∈' x -> T ⊢ wf_class y.
Proof.
  intros H1 H2. apply (wf_source_class_elim H1). intros t.
  apply wf_source_class_intro with t;[apply Ctx;auto|].
  eapply wf_source_transitive_elim.
  - eapply wf_source_tw_transitive,Ctx;auto.
  - apply Ctx;auto.
  - apply (Weak H2). auto.
Qed.

#[local] Instance wf_predicate_dec : eq_dec ZF_pred_sig.
Proof. intros x y. unfold dec. decide equality. Defined.
#[local] Instance wf_function_dec : eq_dec sig_empty.
Proof. intros []. Defined.

Lemma wf_domain_bounded : bounded 1 wf_domain.
Proof.
  apply (proj1 (bounded_comp_eq 1 wf_domain)). unfold wf_domain,wf_class,wf_tw,wf_transitive,
    wf_wellf,wf_subset,wf_nonempty,wf_minimal,wf_minel.
  cbn. repeat split;lia.
Qed.

Print Assumptions wf_domain_bounded.
Print Assumptions wf_source_member.



