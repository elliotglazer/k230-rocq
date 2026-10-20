(** A genuine internally coded finite-prefix map for three arbitrary
    variable names. No bound on those names or external choice is used. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions
  NumericalEnvironments NumericalRenamingMaps.
Unset Implicit Arguments.

Theorem three_name_renaming_total M a b c delta : exists p q,
  renaming_lookup M p q (code_numeral M 3) delta (code_numeral M 0) a /\
  renaming_lookup M p q (code_numeral M 3) delta (code_numeral M 1) b /\
  renaming_lookup M p q (code_numeral M 3) delta (code_numeral M 2) c.
Proof.
  destruct (environment_cons_total M (zeroM M) (zeroM M) (zeroM M) c) as (p1&q1&n1&HC).
  destruct (environment_cons_total M p1 q1 n1 b) as (p2&q2&n2&HB).
  destruct (environment_cons_total M p2 q2 n2 a) as (p3&q3&n3&HA).
  assert (EN:n3=code_numeral M 3).
  { rewrite (proj1 HA),(proj1 HB),(proj1 HC). reflexivity. }
  assert (H0:coding_lt M (code_numeral M 0) n3).
  { rewrite EN. apply coding_zero_lt_succ. }
  assert (H1:coding_lt M (code_numeral M 1) n3).
  { rewrite EN. apply (coding_lt_trans M (code_numeral M 1) (code_numeral M 2) (code_numeral M 3));
      apply coding_lt_succ. }
  assert (H2:coding_lt M (code_numeral M 2) n3).
  { rewrite EN. apply coding_lt_succ. }
  exists p3,q3. rewrite <-EN. split.
  - apply (proj2 (renaming_lookup_inside M p3 q3 n3 delta _ a H0)).
    apply (proj1 (environment_lookup_inside M p3 q3 n3 _ a H0)).
    exact (proj2 (environment_cons_head M p2 q2 n2 a p3 q3 n3 a HA) eq_refl).
  - split.
    + apply (proj2 (renaming_lookup_inside M p3 q3 n3 delta _ b H1)).
      apply (proj1 (environment_lookup_inside M p3 q3 n3 _ b H1)).
      apply (proj2 (environment_cons_tail M p2 q2 n2 a p3 q3 n3 (zeroM M) b HA)).
      exact (proj2 (environment_cons_head M p1 q1 n1 b p2 q2 n2 b HB) eq_refl).
    + apply (proj2 (renaming_lookup_inside M p3 q3 n3 delta _ c H2)).
      apply (proj1 (environment_lookup_inside M p3 q3 n3 _ c H2)).
      apply (proj2 (environment_cons_tail M p2 q2 n2 a p3 q3 n3 (code_numeral M 1) c HA)).
      apply (proj2 (environment_cons_tail M p1 q1 n1 b p2 q2 n2 (zeroM M) c HB)).
      exact (proj2 (environment_cons_head M (zeroM M) (zeroM M) (zeroM M) c p1 q1 n1 c HC) eq_refl).
Qed.

Print Assumptions three_name_renaming_total.
