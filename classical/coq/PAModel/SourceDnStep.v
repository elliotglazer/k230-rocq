(** Exact guarded quantifier step in Z_refl.Dn. A literal beta certificate
    rotates indices0,1,2 to1,2,0 and fixes the remaining free indices. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  NumericalEnvironments NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution RenamingSubstitution
  SourceNumeralLift SubstitutionSource SourceRenamingBounds SourceBounded SetFormulaCodes SchemaRenamingDescriptors.
From FOL.Tennenbaum Require Import Peano.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Lemma source_dn_rotate_zero M :
  renaming_lookup M (code_numeral M 1653) (code_numeral M 6) (code_numeral M 3) (zeroM M)
    (zeroM M) (code_numeral M 1).
Proof.
  apply (proj2 (renaming_lookup_inside M _ _ _ _ _ _ (coding_zero_lt_succ M (code_numeral M 2)))).
  apply (descriptor_beta_certificate M 1653 6 0 1 236);reflexivity||lia.
Qed.
Lemma source_dn_rotate_one M :
  renaming_lookup M (code_numeral M 1653) (code_numeral M 6) (code_numeral M 3) (zeroM M)
    (code_numeral M 1) (code_numeral M 2).
Proof.
  apply (proj2 (renaming_lookup_inside M _ _ _ _ _ _
    ((proj2 (coding_lt_succ_cancel M (zeroM M) (code_numeral M 2))) (coding_zero_lt_succ M (code_numeral M 1))))).
  apply (descriptor_beta_certificate M 1653 6 1 2 127);reflexivity||lia.
Qed.
Lemma source_dn_rotate_two M :
  renaming_lookup M (code_numeral M 1653) (code_numeral M 6) (code_numeral M 3) (zeroM M)
    (code_numeral M 2) (zeroM M).
Proof.
  apply (proj2 (renaming_lookup_inside M _ _ _ _ _ _ (coding_lt_succ M (code_numeral M 2)))).
  apply (descriptor_beta_certificate M 1653 6 2 0 87);reflexivity||lia.
Qed.

Lemma source_dn_rotate_outside M i :
  ~coding_lt M i (code_numeral M 3) ->
  renaming_lookup M (code_numeral M 1653) (code_numeral M 6) (code_numeral M 3) (zeroM M) i i.
Proof.
  intro HI. right. split;[exact HI|]. symmetry. apply coding_add_zero_r.
Qed.

Theorem source_dn_rotate_bounded M phi rotated n :
  source_bounded M phi (succM M (succM M (succM M n))) ->
  numerical_renaming M phi (code_numeral M 1653) (code_numeral M 6) (code_numeral M 3) (zeroM M) rotated ->
  source_bounded M rotated (succM M (succM M (succM M n))).
Proof.
  intros HF HR. apply (numerical_renaming_preserves_bound M phi _ _ _ _ rotated _ _ HF HR).
  intros i j HI HJ. destruct (environment_lt_cases M i (code_numeral M 3)) as [HS|HS].
  - destruct (source_numeral_initial_segment M 3 i HS) as (v & HV & ->).
    destruct v as [|[|[|v]]];try lia.
    + assert (E : j = code_numeral M 1) by (eapply renaming_lookup_functional;[exact HJ|apply source_dn_rotate_zero]).
      subst j. apply coding_lt_succ_cancel,coding_zero_lt_succ.
    + assert (E : j = code_numeral M 2) by (eapply renaming_lookup_functional;[exact HJ|apply source_dn_rotate_one]).
      subst j. apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_zero_lt_succ.
    + assert (E : j = zeroM M) by (eapply renaming_lookup_functional;[exact HJ|apply source_dn_rotate_two]).
      subst j. apply coding_zero_lt_succ.
  - assert (E : j = i) by (eapply renaming_lookup_functional;[exact HJ|apply source_dn_rotate_outside;exact HS]).
    now subst j.
Qed.

Definition source_dn_successor M previous out := exists rotated atom implication,
  numerical_renaming M previous (code_numeral M 1653) (code_numeral M 6) (code_numeral M 3) (zeroM M) rotated /\
  sf_relation M SFMember (zeroM M) (code_numeral M 2) atom /\
  sf_relation M SFImpl atom rotated implication /\ sf_relation M SFAll implication (zeroM M) out.
Definition source_dn_successor_formula (previous out:term) : form :=
  ∃∃∃ (numerical_renaming_formula (lift3 previous) (num 1653) (num 6) (num 3) zero $2 ∧
    (sf_formula SFMember zero (num 2) $1 ∧
    (sf_formula SFImpl $1 $2 $0 ∧ sf_formula SFAll $0 zero (lift3 out)))).
Local Opaque holds numerical_renaming_formula sf_formula.
Theorem source_dn_successor_formula_correct M rho previous out :
  holds M rho (source_dn_successor_formula previous out) <->
  source_dn_successor M (evalM M rho previous) (evalM M rho out).
Proof.
  unfold source_dn_successor_formula,source_dn_successor. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite numerical_renaming_formula_correct.
  setoid_rewrite sf_formula_correct. repeat setoid_rewrite code_eval_num.
  unfold evalM,lift3. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_dn_successor_total M previous : exists out,source_dn_successor M previous out.
Proof.
  destruct (numerical_renaming_total M previous (code_numeral M 1653) (code_numeral M 6) (code_numeral M 3) (zeroM M)) as [rotated HR].
  destruct (sf_relation_total M SFMember (zeroM M) (code_numeral M 2)) as [atom HA].
  destruct (sf_relation_total M SFImpl atom rotated) as [implication HI].
  destruct (sf_relation_total M SFAll implication (zeroM M)) as [out HO].
  exists out,rotated,atom,implication. auto.
Qed.
Theorem source_dn_successor_functional M previous out out' :
  source_dn_successor M previous out -> source_dn_successor M previous out' -> out=out'.
Proof.
  intros (rot & atom & implication & HR & HA & HI & HO) (rot' & atom' & implication' & HR' & HA' & HI' & HO').
  assert (E : rot=rot') by (eapply numerical_renaming_functional;eassumption). subst rot'.
  assert (E : atom=atom') by (eapply sf_relation_functional;eassumption). subst atom'.
  assert (E : implication=implication') by (eapply sf_relation_functional;eassumption). subst implication'.
  exact (sf_relation_functional M SFAll implication (zeroM M) out out' HO HO').
Qed.
Theorem source_dn_successor_bounded M previous out n :
  source_bounded M previous (succM M (succM M (succM M n))) -> source_dn_successor M previous out ->
  source_bounded M out (succM M (succM M n)).
Proof.
  intros HP (rot & atom & implication & HR & HA & HI & HO).
  apply (proj2 (source_bounded_accept_unary M SFAll implication out (succM M (succM M n)) (or_introl eq_refl) HO)).
  apply (proj2 (source_bounded_accept_binary M SFImpl atom rot implication (succM M (succM M (succM M n)))
    (or_intror (or_intror eq_refl)) HI)). split.
  - apply (proj2 (source_bounded_accept_atom M SFMember (zeroM M) (code_numeral M 2) atom
      (succM M (succM M (succM M n))) (or_introl eq_refl) HA)). split.
    + apply coding_zero_lt_succ.
    + apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_zero_lt_succ.
  - exact (source_dn_rotate_bounded M previous rot n HP HR).
Qed.

Print Assumptions source_dn_rotate_bounded.
Print Assumptions source_dn_successor_formula_correct.
Print Assumptions source_dn_successor_total.
Print Assumptions source_dn_successor_functional.
Print Assumptions source_dn_successor_bounded.
