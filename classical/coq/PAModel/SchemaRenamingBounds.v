(** Uniform internal bounds for the four concrete ZFC schema renamings. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions NumericalProofs NumericalEnvironments SourceBounded
  NumericalRenamingMaps NumericalRenaming SourceRenamingBounds SchemaRenamingDescriptors.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition schema_input_bound M s n :=
  match s with SepBody => succM M n | _ => succM M (succM M n) end.
Definition schema_output_bound M s n :=
  match s with RepC => succM M (succM M (succM M (succM M n)))
  | _ => succM M (succM M (succM M n)) end.

Lemma schema_first_bound M s n :
  coding_lt M (code_numeral M (schema_first s)) (schema_output_bound M s n).
Proof.
  destruct s; cbn [schema_first schema_output_bound code_numeral];
    repeat apply (proj2 (coding_lt_succ_cancel M _ _)); apply coding_zero_lt_succ.
Qed.

Lemma schema_second_bound M s n : s <> SepBody ->
  coding_lt M (code_numeral M (schema_second s)) (schema_output_bound M s n).
Proof.
  intro Hs. destruct s; [contradiction| | |];
    cbn [schema_second schema_output_bound code_numeral];
    repeat apply (proj2 (coding_lt_succ_cancel M _ _)); apply coding_zero_lt_succ.
Qed.

Lemma schema_tail_bound M s n i :
  coding_lt M i (schema_input_bound M s n) ->
  coding_lt M (addM M i (code_numeral M (schema_delta s))) (schema_output_bound M s n).
Proof.
  intro Hi. destruct s; cbn [schema_input_bound] in Hi;
    cbn [schema_delta schema_output_bound code_numeral];
    rewrite Arithmetic.add_comm; repeat rewrite Arithmetic.add_succ;
    rewrite Arithmetic.add_zero; repeat apply (proj2 (coding_lt_succ_cancel M _ _)); exact Hi.
Qed.

Theorem schema_lookup_bound M s n i j :
  coding_lt M i (schema_input_bound M s n) -> schema_lookup M s i j ->
  coding_lt M j (schema_output_bound M s n).
Proof.
  intros Hi Hj. destruct (environment_lt_cases M i (code_numeral M (schema_length s))) as [Hin|Hout].
  - assert (Hsmall : i = zeroM M \/ (s <> SepBody /\ i = code_numeral M 1)).
    { destruct s; cbn [schema_length code_numeral] in Hin.
      - apply coding_lt_succ_cases in Hin. destruct Hin as [Hbad|E]; [|now left].
        exfalso. exact (coding_not_lt_zero M i Hbad).
      - apply coding_lt_succ_cases in Hin. destruct Hin as [Hin|E].
        + apply coding_lt_succ_cases in Hin. destruct Hin as [Hbad|E]; [|now left].
          exfalso. exact (coding_not_lt_zero M i Hbad).
        + right. split; [discriminate|exact E].
      - apply coding_lt_succ_cases in Hin. destruct Hin as [Hin|E].
        + apply coding_lt_succ_cases in Hin. destruct Hin as [Hbad|E]; [|now left].
          exfalso. exact (coding_not_lt_zero M i Hbad).
        + right. split; [discriminate|exact E].
      - apply coding_lt_succ_cases in Hin. destruct Hin as [Hin|E].
        + apply coding_lt_succ_cases in Hin. destruct Hin as [Hbad|E]; [|now left].
          exfalso. exact (coding_not_lt_zero M i Hbad).
        + right. split; [discriminate|exact E]. }
    destruct Hsmall as [E|[Hs E]]; subst i.
    + apply schema_lookup_first in Hj. subst j. apply schema_first_bound.
    + apply schema_lookup_second in Hj. subst j. now apply schema_second_bound.
  - apply (proj1 (schema_lookup_tail M s i j Hout)) in Hj. subst j.
    now apply schema_tail_bound.
Qed.

Theorem schema_renaming_bound M s f body n :
  source_bounded M f (schema_input_bound M s n) -> schema_renaming M s f body ->
  source_bounded M body (schema_output_bound M s n).
Proof.
  intros Hf Hr. apply (numerical_renaming_preserves_bound M f
    (code_numeral M (schema_dividend s)) (code_numeral M (schema_modulus s))
    (code_numeral M (schema_length s)) (code_numeral M (schema_delta s)) body
    (schema_input_bound M s n) (schema_output_bound M s n) Hf Hr).
  intros i j Hi Hj. exact (schema_lookup_bound M s n i j Hi Hj).
Qed.

Corollary schema_separation_bound M f body n :
  source_bounded M f (succM M n) -> schema_renaming M SepBody f body ->
  source_bounded M body (succM M (succM M (succM M n))).
Proof. apply (schema_renaming_bound M SepBody f body n). Qed.

Corollary schema_replacement_a_bound M f body n :
  source_bounded M f (succM M (succM M n)) -> schema_renaming M RepA f body ->
  source_bounded M body (succM M (succM M (succM M n))).
Proof. apply (schema_renaming_bound M RepA f body n). Qed.

Corollary schema_replacement_b_bound M f body n :
  source_bounded M f (succM M (succM M n)) -> schema_renaming M RepB f body ->
  source_bounded M body (succM M (succM M (succM M n))).
Proof. apply (schema_renaming_bound M RepB f body n). Qed.

Corollary schema_replacement_c_bound M f body n :
  source_bounded M f (succM M (succM M n)) -> schema_renaming M RepC f body ->
  source_bounded M body (succM M (succM M (succM M (succM M n)))).
Proof. apply (schema_renaming_bound M RepC f body n). Qed.


