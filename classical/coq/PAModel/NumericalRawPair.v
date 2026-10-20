(** A fixed raw-pair proof, transported from the original checked syntactic
    calculus and normalized in an arbitrary arithmetic model. *)
From OldUndecidability.FOL Require Sets.minZF.
From OldZF Require Std_glue Std_tr.
From OldK230S Require KPPair.
From OldK230L Require Comp_Prop230.
From OldFixedTarget Require Positive230.
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions CodeDescent
  NumericalProofs ProofTemplates NamedLeibnizSteps NumericalEquivalence TargetNumeralLift SourceNumeralLift
  ThmConstructorBridge OldNamedSyntaxBridge FiniteNamedPolicies FinitePolicyBounded
  FiniteTemplateRebase QuotientAtomTemplates ZFCFiniteAxiomTemplates
  SourceBoundedCalibration.
From PAModel Require Import RawTemplateSpecialization TemplateNamedSubstitution TemplateBinderFresh.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition raw_pair_source : set_form :=
  isolated_formula OldK230S.KPPair.raw_pair_axiom.
Definition raw_pair_old_expression :=
  isolated_named_expression (OldZF.Std_tr.tr OldZF.Std_glue.eta0
    OldK230S.KPPair.raw_pair_axiom).

Lemma raw_pair_source_closed : bounded 0 raw_pair_source.
Proof. apply set_formula_boundb_sound. vm_compute. reflexivity. Qed.

Theorem numerical_raw_pair_old M :
  ns_proof M (fun _=>zeroM M) raw_pair_old_expression.
Proof.
  intros f HF.
  assert (HP : K230L.Thm230.thm230
    (code_value (fun _=>0) raw_pair_old_expression)).
  { unfold raw_pair_old_expression. rewrite isolated_named_expression_value.
    apply original_thm230_to_current.
    exact (OldFixedTarget.Positive230.K0_to_positive_formula
      OldK230S.KPPair.raw_pair_axiom OldZF.Std_glue.eta0
      OldK230S.KPPair.K0_proves_pair OldZF.Std_glue.oddenv_eta0). }
  pose proof (code_relation_numeral M (fun _=>0) raw_pair_old_expression) as HC.
  assert (E:f=code_numeral M (code_value (fun _=>0) raw_pair_old_expression)).
  { exact (code_relation_functional M raw_pair_old_expression (fun _=>zeroM M) _ _ HF HC). }
  subst f. exact (thm230_numeral_lift M _ HP).
Qed.

Theorem numerical_raw_pair_template M rho fresh k :
  code_relation M rho fresh k -> coding_lt M (zeroM M) k ->
  ns_proof M rho (template_set_formula (fun _=>CEconst 0) fresh raw_pair_source).
Proof.
  intros HK Hk g HG.
  destruct (code_relation_total M raw_pair_old_expression (fun _=>zeroM M)) as [f HF].
  apply (numerical_implies_apply M f g);[|exact (numerical_raw_pair_old M f HF)].
  assert (HE:numerical_equivalent M f g).
  { apply (finite_bounded_depth_to_sequential_codes M raw_pair_source 0
    (fun _=>zeroM M) rho true (fun idx => CEconst (2*idx+1)) (fun _=>CEconst 0)
    (CEconst 0) fresh (CEconst 0)
    (fun idx => code_numeral M (2*idx+1)) (fun _=>zeroM M) k f g).
  - exact raw_pair_source_closed.
  - intros i Hi. lia.
  - intro i. reflexivity.
  - intro i. reflexivity.
  - intros i m Hm. change (code_numeral M (2*m)<>code_numeral M 0).
    apply target_numerals_distinct. lia.
  - exact HK.
  - apply template_hygienic_below;[exact Hk|]. intro i. exact Hk.
  - unfold raw_pair_old_expression in HF.
    rewrite (isolated_tr_named_policy OldK230S.KPPair.raw_pair_axiom
      OldZF.Std_glue.eta0 (fun idx => CEconst (2*idx+1)) (CEconst 0)
      ltac:(intro idx;reflexivity)) in HF. exact HF.
  - exact HG. }
  exact (proj1 HE).
Qed.

Print Assumptions numerical_raw_pair_old.
Print Assumptions numerical_raw_pair_template.

Definition raw_pair_open_source : set_form :=
  ∃ (($2 ∈' $0 ∧ $1 ∈' $0) ∧
    ∀ ($0 ∈' $1 → ($0 ≡' $3 ∨ $0 ≡' $2))).

Definition E_raw_pair a b c z :=
  E_wa (E_wa (E_wel a c) (E_wel b c))
    (E_wal z (E_wim (E_wel z c) (E_or (E_weq z a) (E_weq z b)))).

Lemma raw_pair_source_unfold : raw_pair_source = ∀ ∀ raw_pair_open_source.
Proof. reflexivity. Qed.

Theorem numerical_raw_pair_named M rho A B fresh a b k :
  code_relation M rho A a -> code_relation M rho B b ->
  code_relation M rho fresh k -> coding_lt M (zeroM M) k ->
  coding_lt M a k -> coding_lt M b k ->
  ns_proof M rho
    (E_wex (CEadd (CEadd fresh (CEconst 1)) (CEconst 1))
      (E_raw_pair A B (CEadd (CEadd fresh (CEconst 1)) (CEconst 1))
        (CEadd (CEadd (CEadd fresh (CEconst 1)) (CEconst 1)) (CEconst 1)))).
Proof.
  intros HA HB HF H0 HA0 HB0.
  set (f1:=CEadd fresh (CEconst 1)).
  set (f2:=CEadd f1 (CEconst 1)).
  assert (HF1:code_relation M rho f1 (succM M k))
    by (unfold f1;now apply template_fresh_increment_graph).
  assert (HF2:code_relation M rho f2 (succM M (succM M k)))
    by (unfold f2;now apply template_fresh_increment_graph).
  assert (HA1:coding_lt M a (succM M k)) by
    exact (coding_lt_trans M a k (succM M k) HA0 (coding_lt_succ M k)).
  assert (HB1:coding_lt M b (succM M k)) by
    exact (coding_lt_trans M b k (succM M k) HB0 (coding_lt_succ M k)).
  assert (HB2:coding_lt M b (succM M (succM M k))) by
    exact (coding_lt_trans M b (succM M k) _ HB1 (coding_lt_succ M _)).
  assert (H01:coding_lt M (zeroM M) (succM M k)) by apply coding_zero_lt_succ.
  assert (H2:ns_proof M rho
    (template_set_formula (B .: A .: fun _=>CEconst 0) f2 raw_pair_open_source)).
  { apply (ns_proof_mp M rho
      (E_wal f1 (template_set_formula (f1 .: A .: fun _=>CEconst 0) f2 raw_pair_open_source))).
    - apply (ns_proof_mp M rho
        (E_wal fresh (template_set_formula (fresh .: fun _=>CEconst 0) f1
          (∀ raw_pair_open_source)))).
      + pose proof (numerical_raw_pair_template M rho fresh k HF H0) as HP.
        rewrite raw_pair_source_unfold in HP. exact HP.
      + apply (finite_template_specialization M (∀ raw_pair_open_source)
          rho fresh A (fun _=>CEconst 0) f1 k a (succM M k)
          HF HA HF1).
        * exact (template_lt_different M (zeroM M) k H0).
        * exact (template_lt_different M a k HA0).
        * apply coding_lt_succ.
        * exact HA1.
        * intros idx v HV. change (v=zeroM M) in HV. subst v.
          intro E. apply (template_lt_different M (zeroM M) k H0). symmetry;exact E.
    - apply (finite_template_specialization M raw_pair_open_source
        rho f1 B (A .: fun _=>CEconst 0) f2 (succM M k) b (succM M (succM M k))
        HF1 HB HF2).
      + exact (template_lt_different M (zeroM M) (succM M k) H01).
      + exact (template_lt_different M b (succM M k) HB1).
      + apply coding_lt_succ.
      + exact HB2.
      + intros [|idx] v HV;cbn in HV.
        * rewrite (code_relation_functional M A rho v a HV HA).
          intro E. apply (template_lt_different M a (succM M k) HA1). symmetry;exact E.
        * change (v=zeroM M) in HV. subst v.
          intro E. apply (template_lt_different M (zeroM M) (succM M k) H01). symmetry;exact E. }
  exact H2.
Qed.

Print Assumptions numerical_raw_pair_named.
