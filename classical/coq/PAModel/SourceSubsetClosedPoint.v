(** The subset-closed carrier law, with actual arbitrary-model parameter
    specialization and an ordinary source-calculus consumer. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds FixedSourceBounds SourceBounded NumericalContexts NumericalSourceFull
  SourceNumeralLift SourceFiniteParameters SourceFiniteParameterProofs
  ThreeNameRenaming NumericalRenamingMaps NumericalContextRenaming
  SourceProofRenaming SourceProofWeakening SourceDerivedRules.
From Undecidability.FOL Require Import Syntax.Facts Deduction.FullNDFacts Sets.minZF.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Open Scope minZFsyn.
Set Implicit Arguments.
#[local] Instance subset_point_pc : peirce := class.
#[local] Hint Constructors prv : core.

Definition source_point_raw_subset (a b:sf_term) :sf_form :=
  ∀($0 ∈' a`[↑] → $0 ∈' b`[↑]).
Definition source_point_subset_closed (b:sf_term) :sf_form :=
  ∀($0 ∈' b`[↑] → ∀(source_point_raw_subset $0 $1 → $0 ∈' b`[↑]`[↑])).
Definition source_subset_closed_point :sf_form :=
  source_point_subset_closed $0 → $1 ∈' $0 → source_point_raw_subset $2 $1 → $2 ∈' $0.

Lemma source_subset_closed_point_finite : (@nil sf_form) ⊢ source_subset_closed_point.
Proof.
  unfold source_subset_closed_point. apply II.
  assert (HP:(source_point_subset_closed $0::nil) ⊢ source_point_subset_closed $0)
    by (apply Ctx;cbn;auto).
  unfold source_point_subset_closed in HP.
  apply (AllE $1) in HP. cbn in HP.
  change ((source_point_subset_closed $0::nil) ⊢
    $1 ∈' $0 → ∀(source_point_raw_subset $0 $2 → $0 ∈' $1)) in HP.
  apply II. assert (HP' : (($1 ∈' $0)::source_point_subset_closed $0::nil) ⊢
    $1 ∈' $0 → ∀(source_point_raw_subset $0 $2 → $0 ∈' $1)).
  { eapply Weak;[exact HP|]. intros f HF. cbn in HF |-*. tauto. }
  assert (HX:(($1 ∈' $0)::source_point_subset_closed $0::nil) ⊢ $1 ∈' $0)
    by (apply Ctx;cbn;auto).
  pose proof (IE HP' HX) as HQ. apply (AllE $2) in HQ.
  unfold source_point_raw_subset in *. cbn in HQ. exact HQ.
Qed.

Unset Implicit Arguments.

Lemma source_empty_three_parameter_proof M (phi:sf_form) rho out :
  (@nil sf_form) ⊢ phi ->
  code_relation M rho (source_parameter_expression source_three_parameter_names phi) out ->
  source_full_prv M (zeroM M)(zeroM M)(zeroM M) out.
Proof.
  intros HP HO.
  destruct (three_name_renaming_total M (rho 0)(rho 1)(rho 2)(zeroM M))
    as (b&c&H0&H1&H2).
  apply (source_full_prv_renaming M (zeroM M)(zeroM M)(zeroM M)
    (code_numeral M (sf_encode phi)) b c (code_numeral M 3)(zeroM M)
    (zeroM M)(zeroM M) out).
  - exact (source_full_forward_model_empty M phi HP).
  - apply context_renaming_empty.
  - apply (source_finite_parameter_renaming M phi source_three_parameter_names rho
      b c (code_numeral M 3)(zeroM M) out);[|exact HO].
    intros [|[|[|i]]] x HX;cbn [source_three_parameter_names] in HX.
    + change (x=rho 0) in HX. now subst x.
    + change (x=rho 1) in HX. now subst x.
    + change (x=rho 2) in HX. now subst x.
    + change (x=code_numeral M (S(S(S i)))) in HX. subst x.
      assert (HOutside:~coding_lt M (code_numeral M (S(S(S i)))) (code_numeral M 3)).
      { intro HBad. apply (proj1 (fixed_source_numeral_lt_iff M (S(S(S i))) 3)) in HBad. lia. }
      apply (proj2 (renaming_lookup_outside M b c (code_numeral M 3)(zeroM M)
        (code_numeral M (S(S(S i)))) (code_numeral M (S(S(S i)))) HOutside)).
      symmetry. apply coding_add_zero_r.
Qed.

Theorem numerical_subset_closed_point_empty M rho out :
  code_relation M rho (source_parameter_expression source_three_parameter_names source_subset_closed_point) out ->
  source_full_prv M (zeroM M)(zeroM M)(zeroM M) out.
Proof. exact (source_empty_three_parameter_proof M source_subset_closed_point rho out source_subset_closed_point_finite). Qed.

Theorem numerical_subset_closed_point M db dc dn rho closed member subset result :
  code_relation M rho (source_parameter_expression source_three_parameter_names
    (source_point_subset_closed $0)) closed ->
  code_relation M rho (source_parameter_expression source_three_parameter_names ($1 ∈' $0)) member ->
  code_relation M rho (source_parameter_expression source_three_parameter_names
    (source_point_raw_subset $2 $1)) subset ->
  code_relation M rho (source_parameter_expression source_three_parameter_names ($2 ∈' $0)) result ->
  source_full_prv M db dc dn closed ->source_full_prv M db dc dn member ->
  source_full_prv M db dc dn subset ->source_full_prv M db dc dn result.
Proof.
  intros HC HM HS HR PC PM PS.
  destruct (sf_relation_total M SFImpl subset result) as (last&HL).
  destruct (sf_relation_total M SFImpl member last) as (middle&HI).
  destruct (sf_relation_total M SFImpl closed middle) as (out&HO).
  assert (HLast:code_relation M rho
    (source_parameter_expression source_three_parameter_names
      (source_point_raw_subset $2 $1 → $2 ∈' $0)) last).
  { exact (proj2 (schema_expression_graph M rho SFImpl _ _ subset result last HS HR) HL). }
  assert (HMiddle:code_relation M rho
    (source_parameter_expression source_three_parameter_names
      ($1 ∈' $0 → source_point_raw_subset $2 $1 → $2 ∈' $0)) middle).
  { exact (proj2 (schema_expression_graph M rho SFImpl _ _ member last middle HM HLast) HI). }
  assert (HOut:code_relation M rho
    (source_parameter_expression source_three_parameter_names source_subset_closed_point) out).
  { exact (proj2 (schema_expression_graph M rho SFImpl _ _ closed middle out HC HMiddle) HO). }
  pose proof (numerical_subset_closed_point_empty M rho out HOut) as PE.
  destruct (source_full_prv_wellformed M db dc dn closed PC) as (k&_&HB).
  assert (PO:source_full_prv M db dc dn out).
  { apply (source_full_prv_weaken_bounded M (zeroM M)(zeroM M)(zeroM M) db dc dn out k PE);[|exact HB].
    intros f HF. exfalso. exact (context_empty M (zeroM M)(zeroM M) f HF). }
  exact (source_full_modus_ponens M db dc dn subset result last HL
    (source_full_modus_ponens M db dc dn member last middle HI
      (source_full_modus_ponens M db dc dn closed middle out HO PO PC) PM) PS).
Qed.

Print Assumptions source_subset_closed_point_finite.
Print Assumptions numerical_subset_closed_point_empty.
Print Assumptions numerical_subset_closed_point.
