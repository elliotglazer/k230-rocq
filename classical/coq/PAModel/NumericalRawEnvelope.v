(** A fixed envelope instance of augmented Separation. This lifts a finite
    syntactic proof and gives actual numerical K proofs in every PA model. *)
From OldZF Require Std_glue Std_tr.
From OldK230S Require KPSeparation KDomain.
From OldFixedTarget Require Positive230.
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  CodeDescent NumericalProofs ProofTemplates NamedLeibnizSteps NumericalEquivalence
  TargetNumeralLift SourceNumeralLift ThmConstructorBridge OldNamedSyntaxBridge
  FiniteNamedPolicies FinitePolicyBounded FiniteTemplateRebase QuotientAtomTemplates
  ZFCFiniteAxiomTemplates SourceBoundedCalibration RawTemplateSpecialization
  TemplateNamedSubstitution TemplateBinderFresh.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition old_envelope_source := OC.FullSyntax.forall_times 1
  (OldK230S.KPSeparation.augmented_separation OldK230S.KDomain.domain_selector).
Definition raw_envelope_source : set_form := isolated_formula old_envelope_source.
Definition raw_envelope_old_expression :=
  isolated_named_expression (OldZF.Std_tr.tr OldZF.Std_glue.eta0 old_envelope_source).

Lemma raw_envelope_source_closed : bounded 0 raw_envelope_source.
Proof. apply set_formula_boundb_sound. vm_compute. reflexivity. Qed.

Theorem numerical_raw_envelope_old M :
  ns_proof M (fun _=>zeroM M) raw_envelope_old_expression.
Proof.
  intros f HF.
  assert (HP : K230L.Thm230.thm230
    (code_value (fun _=>0) raw_envelope_old_expression)).
  { unfold raw_envelope_old_expression. rewrite isolated_named_expression_value.
    apply original_thm230_to_current.
    apply (OldFixedTarget.Positive230.K0_to_positive_formula old_envelope_source
      OldZF.Std_glue.eta0);[|exact OldZF.Std_glue.oddenv_eta0].
    exact (OldK230S.KPSeparation.K0_proves_augmented_separation 1
      OldK230S.KDomain.domain_selector OldK230S.KDomain.domain_selector_bounded). }
  pose proof (code_relation_numeral M (fun _=>0) raw_envelope_old_expression) as HC.
  assert (E:f=code_numeral M (code_value (fun _=>0) raw_envelope_old_expression)).
  { exact (code_relation_functional M raw_envelope_old_expression
      (fun _=>zeroM M) _ _ HF HC). }
  subst f. exact (thm230_numeral_lift M _ HP).
Qed.

Theorem numerical_raw_envelope_template M rho fresh k :
  code_relation M rho fresh k -> coding_lt M (zeroM M) k ->
  ns_proof M rho (template_set_formula (fun _=>CEconst 0) fresh raw_envelope_source).
Proof.
  intros HK Hk g HG.
  destruct (code_relation_total M raw_envelope_old_expression (fun _=>zeroM M)) as [f HF].
  apply (numerical_implies_apply M f g);[|exact (numerical_raw_envelope_old M f HF)].
  assert (HE:numerical_equivalent M f g).
  { apply (finite_bounded_depth_to_sequential_codes M raw_envelope_source 0
      (fun _=>zeroM M) rho true (fun idx=>CEconst (2*idx+1)) (fun _=>CEconst 0)
      (CEconst 0) fresh (CEconst 0) (fun idx=>code_numeral M (2*idx+1))
      (fun _=>zeroM M) k f g).
    - exact raw_envelope_source_closed.
    - intros i Hi. lia.
    - intro i. reflexivity.
    - intro i. reflexivity.
    - intros i m Hm. change (code_numeral M (2*m)<>code_numeral M 0).
      apply target_numerals_distinct. lia.
    - exact HK.
    - apply template_hygienic_below;[exact Hk|]. intro i. exact Hk.
    - unfold raw_envelope_old_expression in HF.
      rewrite (isolated_tr_named_policy old_envelope_source OldZF.Std_glue.eta0
        (fun idx=>CEconst (2*idx+1)) (CEconst 0) ltac:(intro idx;reflexivity)) in HF.
      exact HF.
    - exact HG. }
  exact (proj1 HE).
Qed.

Definition raw_envelope_open_source : set_form :=
  ∃ ∀ ($0 ∈' $1 ↔ ($0 ≡' $2 ∨ ($0 ∈' $2 ∧ $3 ∈' $0))).
Definition E_raw_envelope t a b x :=
  E_wal x (E_wa
    (E_wim (E_wel x b) (E_or (E_weq x a) (E_wa (E_wel x a) (E_wel t x))))
    (E_wim (E_or (E_weq x a) (E_wa (E_wel x a) (E_wel t x))) (E_wel x b))).

Lemma raw_envelope_source_unfold : raw_envelope_source = ∀ ∀ raw_envelope_open_source.
Proof. reflexivity. Qed.

Theorem numerical_raw_envelope_named M rho T A fresh t a k :
  code_relation M rho T t -> code_relation M rho A a ->
  code_relation M rho fresh k -> coding_lt M (zeroM M) k ->
  coding_lt M t k -> coding_lt M a k ->
  ns_proof M rho
    (E_wex (CEadd (CEadd fresh (CEconst 1)) (CEconst 1))
      (E_raw_envelope T A (CEadd (CEadd fresh (CEconst 1)) (CEconst 1))
        (CEadd (CEadd (CEadd fresh (CEconst 1)) (CEconst 1)) (CEconst 1)))).
Proof.
  intros HT HA HF H0 HT0 HA0.
  set (f1:=CEadd fresh (CEconst 1)).
  set (f2:=CEadd f1 (CEconst 1)).
  assert (HF1:code_relation M rho f1 (succM M k))
    by (unfold f1;now apply template_fresh_increment_graph).
  assert (HF2:code_relation M rho f2 (succM M (succM M k)))
    by (unfold f2;now apply template_fresh_increment_graph).
  assert (HT1:coding_lt M t (succM M k)) by
    exact (coding_lt_trans M t k (succM M k) HT0 (coding_lt_succ M k)).
  assert (HA1:coding_lt M a (succM M k)) by
    exact (coding_lt_trans M a k (succM M k) HA0 (coding_lt_succ M k)).
  assert (HA2:coding_lt M a (succM M (succM M k))) by
    exact (coding_lt_trans M a (succM M k) _ HA1 (coding_lt_succ M _)).
  assert (H01:coding_lt M (zeroM M) (succM M k)) by apply coding_zero_lt_succ.
  assert (H2:ns_proof M rho
    (template_set_formula (A .: T .: fun _=>CEconst 0) f2 raw_envelope_open_source)).
  { apply (ns_proof_mp M rho
      (E_wal f1 (template_set_formula (f1 .: T .: fun _=>CEconst 0) f2 raw_envelope_open_source))).
    - apply (ns_proof_mp M rho
        (E_wal fresh (template_set_formula (fresh .: fun _=>CEconst 0) f1
          (∀ raw_envelope_open_source)))).
      + pose proof (numerical_raw_envelope_template M rho fresh k HF H0) as HP.
        rewrite raw_envelope_source_unfold in HP. exact HP.
      + apply (finite_template_specialization M (∀ raw_envelope_open_source)
          rho fresh T (fun _=>CEconst 0) f1 k t (succM M k) HF HT HF1).
        * exact (template_lt_different M (zeroM M) k H0).
        * exact (template_lt_different M t k HT0).
        * apply coding_lt_succ.
        * exact HT1.
        * intros idx v HV. change (v=zeroM M) in HV. subst v.
          intro E. apply (template_lt_different M (zeroM M) k H0). symmetry;exact E.
    - apply (finite_template_specialization M raw_envelope_open_source
        rho f1 A (T .: fun _=>CEconst 0) f2 (succM M k) a (succM M (succM M k)) HF1 HA HF2).
      + exact (template_lt_different M (zeroM M) (succM M k) H01).
      + exact (template_lt_different M a (succM M k) HA1).
      + apply coding_lt_succ.
      + exact HA2.
      + intros [|idx] v HV;cbn in HV.
        * rewrite (code_relation_functional M T rho v t HV HT).
          intro E. apply (template_lt_different M t (succM M k) HT1). symmetry;exact E.
        * change (v=zeroM M) in HV. subst v.
          intro E. apply (template_lt_different M (zeroM M) (succM M k) H01). symmetry;exact E. }
  exact H2.
Qed.

Print Assumptions numerical_raw_envelope_old.
Print Assumptions numerical_raw_envelope_template.
Print Assumptions numerical_raw_envelope_named.
