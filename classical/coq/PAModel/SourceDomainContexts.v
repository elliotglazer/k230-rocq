(** Exact-length arithmetic tables of the domain assumptions
    D(0),...,D(k-1), for an arbitrary model-valued bound k. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula
  CodeExpressions NumericalProofs NumericalEnvironments NumericalContexts
  NumericalContextRenaming InternalRecursion BetaExtension ProofClosure
  NumericalInstantiation SourceBounded SentenceBounds SourceDomainInstances.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_domain_context M domain k b c :=
  forall i f,coding_lt M i k -> beta M b c i f -> numerical_instantiation M domain i f.

Definition source_domain_context_formula (domain k b c : term) : form :=
  ∀∀ (Peano.sless $1 (environment_lift2 k) →
    beta_formula (environment_lift2 b) (environment_lift2 c) $1 $0 →
    numerical_instantiation_formula (environment_lift2 domain) $1 $0).

Local Opaque holds beta_formula numerical_instantiation_formula.
Theorem source_domain_context_formula_correct M rho domain k b c :
  holds M rho (source_domain_context_formula domain k b c) <->
  source_domain_context M (evalM M rho domain) (evalM M rho k)
    (evalM M rho b) (evalM M rho c).
Proof.
  unfold source_domain_context_formula,source_domain_context.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_sless. setoid_rewrite beta_formula_correct.
  setoid_rewrite numerical_instantiation_formula_correct.
  setoid_rewrite environment_eval_lift2. reflexivity.
Qed.

Definition source_domain_context_step : form := numerical_instantiation_formula $4 $1 $0.

Lemma source_domain_context_step_correct M domain b c i f :
  recursion_step M source_domain_context_step (domain .: fun _=>zeroM M) b c i f <->
  numerical_instantiation M domain i f.
Proof. unfold recursion_step,source_domain_context_step.
  rewrite numerical_instantiation_formula_correct. reflexivity. Qed.

Theorem source_domain_context_total M domain k :
  exists b c,source_domain_context M domain k b c.
Proof.
  assert (HT:forall b c i,exists f,recursion_step M source_domain_context_step
    (domain .: fun _=>zeroM M) b c i f).
  { intros b c i. destruct (numerical_instantiation_total M domain i) as [f HF].
    exists f. apply source_domain_context_step_correct,HF. }
  assert (HP:forall b c b' c' i,prefix M b c b' c' i -> forall f,
    (recursion_step M source_domain_context_step (domain .: fun _=>zeroM M) b c i f <->
     recursion_step M source_domain_context_step (domain .: fun _=>zeroM M) b' c' i f)).
  { intros. rewrite !source_domain_context_step_correct. reflexivity. }
  destruct (recursion_table_total M source_domain_context_step
    (domain .: fun _=>zeroM M) HT HP k) as [b [c H]].
  exists b,c. intros i f HI HF. exact (proj1 (source_domain_context_step_correct M domain b c i f) (H i f HI HF)).
Qed.

Theorem source_domain_context_functional M domain k b c d e :
  source_domain_context M domain k b c -> source_domain_context M domain k d e ->
  forall i f g,coding_lt M i k -> beta M b c i f -> beta M d e i g -> f=g.
Proof.
  intros HB HD i f g HI HF HG.
  exact (numerical_instantiation_functional M domain i f g (HB i f HI HF) (HD i g HI HG)).
Qed.

Theorem source_domain_context_member_iff M domain k b c f :
  source_domain_context M domain k b c ->
  (context_member M b c k f <-> exists i,coding_lt M i k /\ numerical_instantiation M domain i f).
Proof.
  intro H. split.
  - intros [i [HI HF]]. exists i. split;[exact HI|exact (H i f HI HF)].
  - intros [i [HI HF]]. destruct (beta_total M b c i) as [g HG].
    pose proof (numerical_instantiation_functional M domain i f g HF (H i g HI HG)) as E.
    subst g. exists i. auto.
Qed.

Theorem source_domain_context_bounded M domain k b c :
  source_bounded M domain (code_numeral M 1) ->
  source_domain_context M domain k b c -> context_bounded M b c k k.
Proof.
  intros HD HC f [i [HI HF]].
  exact (source_domain_instance_bound M domain i f k HD HI (HC i f HI HF)).
Qed.

Theorem source_domain_context_empty M domain b c :
  source_domain_context M domain (zeroM M) b c.
Proof. intros i f HI _. exfalso. exact (coding_not_lt_zero M i HI). Qed.

Theorem source_domain_context_cons_shift M domain k b c u v b' c' k' :
  source_bounded M domain (code_numeral M 1) ->
  source_domain_context M domain k b c -> context_shift M b c k u v ->
  environment_cons M u v k domain b' c' k' ->
  source_domain_context M domain k' b' c'.
Proof.
  intros HD HC HS HCons i f HI HF. pose proof (proj1 HCons) as EK.
  apply (proj2 (environment_lookup_inside M b' c' k' i f HI)) in HF.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[j E]];subst i.
  - apply (proj1 (environment_cons_head M u v k domain b' c' k' f HCons)) in HF.
    subst f. exact (source_domain_instance_zero M domain HD).
  - apply (proj1 (environment_cons_tail M u v k domain b' c' k' j f HCons)) in HF.
    rewrite EK in HI. apply (proj1 (coding_lt_succ_cancel M j k)) in HI.
    apply (proj1 (environment_lookup_inside M u v k j f HI)) in HF.
    destruct (beta_total M b c j) as [g HG].
    exact (source_domain_instance_shift M domain j g f HD (HC j g HI HG)
      (HS j g f HI HG HF)).
Qed.

Theorem source_domain_context_formula_bound :
  bounded 4 (source_domain_context_formula $0 $1 $2 $3).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Print Assumptions source_domain_context_total.
Print Assumptions source_domain_context_functional.
Print Assumptions source_domain_context_member_iff.
Print Assumptions source_domain_context_bounded.
Print Assumptions source_domain_context_cons_shift.


