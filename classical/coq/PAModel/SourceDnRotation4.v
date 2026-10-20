(** Literal four-cycle used to keep two ordinal names outside Dn binders. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  NumericalEnvironments NumericalRenamingMaps NumericalRenaming SourceNumeralLift SourceDnStep SourceBounded
  SourceRenamingBounds SchemaRenamingDescriptors FixedSourceBounds.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition source_dn_rotate4_index (i:nat) := match i with 0=>1|1=>2|2=>3|3=>0|_=>i end.
Definition source_dn_rotate4 M f g := numerical_renaming M f
  (code_numeral M 5475)(code_numeral M 6)(code_numeral M 4)(zeroM M) g.

Theorem source_dn_rotate4_fixed M i : (i<4)%nat ->
  renaming_lookup M (code_numeral M 5475)(code_numeral M 6)(code_numeral M 4)(zeroM M)
    (code_numeral M i)(code_numeral M(source_dn_rotate4_index i)).
Proof.
  intro HI. apply (proj2 (renaming_lookup_inside M _ _ _ _ _ _
    (proj2 (fixed_source_numeral_lt_iff M i 4) HI))).
  destruct i as [|[|[|[|i]]]];try lia.
  - apply (descriptor_beta_certificate M 5475 6 0 1 782);reflexivity||lia.
  - apply (descriptor_beta_certificate M 5475 6 1 2 421);reflexivity||lia.
  - apply (descriptor_beta_certificate M 5475 6 2 3 288);reflexivity||lia.
  - apply (descriptor_beta_certificate M 5475 6 3 0 219);reflexivity||lia.
Qed.

Theorem source_dn_rotate4_outside M i : ~coding_lt M i(code_numeral M 4) ->
  renaming_lookup M (code_numeral M 5475)(code_numeral M 6)(code_numeral M 4)(zeroM M) i i.
Proof. intro HI. right. split;[exact HI|]. symmetry. apply coding_add_zero_r. Qed.

Theorem source_dn_rotate4_bounded M f g k :
  source_bounded M f(succM M(succM M(succM M(succM M k)))) ->
  source_dn_rotate4 M f g ->source_bounded M g(succM M(succM M(succM M(succM M k)))).
Proof.
  intros HF HR. apply (numerical_renaming_preserves_bound M f _ _ _ _ g _ _ HF HR).
  intros i j HI HJ. destruct (environment_lt_cases M i(code_numeral M 4)) as [HS|HS].
  - destruct (source_numeral_initial_segment M 4 i HS) as (v&HV&->).
    assert(E:j=code_numeral M(source_dn_rotate4_index v)).
    { eapply renaming_lookup_functional;[exact HJ|apply source_dn_rotate4_fixed;exact HV]. }
    subst j. destruct v as [|[|[|[|v]]]];try lia.
    + apply coding_lt_succ_cancel,coding_zero_lt_succ.
    + apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_zero_lt_succ.
    + apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_lt_succ_cancel,coding_zero_lt_succ.
    + apply coding_zero_lt_succ.
  - assert(E:j=i) by (eapply renaming_lookup_functional;[exact HJ|apply source_dn_rotate4_outside;exact HS]).
    now subst j.
Qed.

Print Assumptions source_dn_rotate4_fixed.
Print Assumptions source_dn_rotate4_outside.
Print Assumptions source_dn_rotate4_bounded.
