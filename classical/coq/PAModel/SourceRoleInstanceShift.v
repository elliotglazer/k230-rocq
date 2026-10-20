(** Inserting a free variable commutes with an actual two-role instance.
    The protected abstract roles are shifted by the explicit beta prefix. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
  SourceBounded SourceRoleReopening SourceFiniteCutoffShift SourceCutoffShiftCommutation
  SourceRenamingSquare SourceFilteredProfileShift SourceQuantifierRules
  SourceSubstitutionBounds SourceSubstitutionIdentity SourceBoundMonotone.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Lemma source_role_instance_tail M b c i :
  substitution_lookup M b c (code_numeral M 2) (code_numeral M 2)
    (succM M (succM M i)) (succM M (succM M i)).
Proof.
  right. split.
  - intro H. exact (coding_not_lt_zero M i (proj1 (coding_lt_succ_cancel M i (zeroM M))
      (proj1 (coding_lt_succ_cancel M (succM M i) (code_numeral M 1)) H))).
  - exists i. split;change (succM M (succM M i)=addM M (succM M (succM M (zeroM M))) i);
      now rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
Qed.

Lemma source_role_instance_head M v d b c :source_role_reopening M v d b c ->
  substitution_lookup M b c (code_numeral M 2) (code_numeral M 2) (zeroM M) d /\
  substitution_lookup M b c (code_numeral M 2) (code_numeral M 2) (code_numeral M 1) v.
Proof.
  intros [HD HV]. split.
  - apply (proj2 (substitution_lookup_inside M b c _ _ _ _ (coding_zero_lt_succ M (code_numeral M 1)))).
    exact (proj1 (substitution_lookup_inside M b c _ _ _ _ (coding_zero_lt_succ M (code_numeral M 1))) HD).
  - apply (proj2 (substitution_lookup_inside M b c _ _ _ _ (coding_lt_succ M (code_numeral M 1)))).
    exact (proj1 (substitution_lookup_inside M b c _ _ _ _ (coding_lt_succ M (code_numeral M 1))) HV).
Qed.

Theorem source_role_instance_bounded M phi v d b c result k l :
  source_bounded M phi k ->source_role_reopening M v d b c ->
  numerical_substitution M phi b c (code_numeral M 2) (code_numeral M 2) result ->
  coding_lt M k (succM M l) ->coding_lt M v l ->coding_lt M d l ->source_bounded M result l.
Proof.
  intros HB HRole HS HK HV HD.
  pose proof (source_bounded_monotone M phi k l HB HK) as HBL.
  destruct (source_role_instance_head M v d b c HRole) as (HHead&HTwo).
  apply (numerical_substitution_preserves_bound M phi b c (code_numeral M 2) (code_numeral M 2)
    result l l HBL HS).
  intros i j HI HJ.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[idx E]];subst i.
  - pose proof (substitution_lookup_functional M b c _ _ _ j d HJ HHead) as EJ. now subst j.
  - destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) idx) as [E|[idx' E]];subst idx.
    + pose proof (substitution_lookup_functional M b c _ _ _ j v HJ HTwo) as EJ. now subst j.
    + pose proof (substitution_lookup_functional M b c _ _ _ j _ HJ
        (source_role_instance_tail M b c idx')) as EJ. now subst j.
Qed.

Theorem source_role_instance_identity M phi b c k :source_bounded M phi k ->
  source_role_reopening M (code_numeral M 1) (zeroM M) b c ->
  numerical_substitution M phi b c (code_numeral M 2) (code_numeral M 2) phi.
Proof.
  intros HB HRole. destruct (source_role_instance_head M (code_numeral M 1) (zeroM M) b c HRole)
    as (HZero&HOne).
  apply (numerical_substitution_identity_on_bound M phi b c (code_numeral M 2) (code_numeral M 2) k HB).
  intros i HI. destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[idx E]];subst i;[exact HZero|].
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) idx) as [E|[idx' E]];subst idx;
    [exact HOne|apply source_role_instance_tail].
Qed.

Theorem source_role_instance_shift M phi phi' v d b c result result' sb sc k :
  source_bounded M phi k ->source_cutoff_shift M 2 phi phi' ->
  source_role_reopening M v d b c ->
  numerical_substitution M phi b c (code_numeral M 2) (code_numeral M 2) result ->
  source_formula_shift M result result' ->source_role_reopening M (succM M v) (succM M d) sb sc ->
  numerical_substitution M phi' sb sc (code_numeral M 2) (code_numeral M 2) result'.
Proof.
  intros HB (rb&rc&rn&HM&HR) HRole HSub HShift HRole'.
  destruct (source_role_instance_head M v d b c HRole) as (HD&HV).
  destruct (source_role_instance_head M (succM M v) (succM M d) sb sc HRole') as (HD'&HV').
  apply (numerical_source_renaming_square M phi k b c (code_numeral M 2) (code_numeral M 2)
    rb rc rn (code_numeral M 1) (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1)
    sb sc (code_numeral M 2) (code_numeral M 2) result phi' result' HB HSub
    (source_cutoff_shift_map_renaming M 2 phi phi' rb rc rn HM HR) HShift).
  intros i j l m HI HS HJ HL.
  apply (proj1 (source_cutoff_shift_map_renaming_lookup M 2 rb rc rn i l HM)) in HL.
  pose proof (renaming_lookup_functional M (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M 1) j m (succM M j) HJ (source_shift_map_lookup M j)) as EM. subst m.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[idx E]];subst i.
  - pose proof (substitution_lookup_functional M b c _ _ _ j d HS HD) as EJ. subst j.
    pose proof (substitution_lookup_functional M rb rc rn (code_numeral M 3) _ l _ HL
      (source_cutoff_shift_map_fixed_lookup M 2 rb rc rn HM 0)) as EL. now subst l.
  - destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) idx) as [E|[idx' E]];subst idx.
    + pose proof (substitution_lookup_functional M b c _ _ _ j v HS HV) as EJ. subst j.
      pose proof (substitution_lookup_functional M rb rc rn (code_numeral M 3) _ l _ HL
        (source_cutoff_shift_map_fixed_lookup M 2 rb rc rn HM 1)) as EL. now subst l.
    + pose proof (substitution_lookup_functional M b c _ _ _ j _ HS
        (source_role_instance_tail M b c idx')) as EJ. subst j.
      pose proof (substitution_lookup_functional M rb rc rn (code_numeral M 3) _ l _ HL
        (source_cutoff_shift_map_tail_lookup M 2 rb rc rn idx' HM)) as EL. subst l.
      exact (source_role_instance_tail M sb sc (succM M idx')).
Qed.

Print Assumptions source_role_instance_shift.
Print Assumptions source_role_instance_bounded.
Print Assumptions source_role_instance_identity.
