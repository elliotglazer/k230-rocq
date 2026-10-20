(** Simultaneous application of an arbitrary internal binary source matrix
    to named input/output roles. This is an actual substitution graph. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded SourceNumeralLift
  NumericalSubstitutionMaps NumericalSubstitution SourceSubstitutionBounds SourceSubstitutionComposition
  SourceRoleReopening SourcePieceClosure SourcePieceClosureFacts SourcePieceRoles.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition source_rec_binary M phi u v out:=exists b c,
  source_role_reopening M v u b c /\numerical_substitution M phi b c(code_numeral M 2)(code_numeral M 2)out.
Theorem source_rec_binary_total M phi u v:exists out,source_rec_binary M phi u v out.
Proof.
  destruct(source_role_reopening_total M v u) as(b&c&HM).
  destruct(numerical_substitution_total M phi b c(code_numeral M 2)(code_numeral M 2)) as(out&HO).
  exists out,b,c. auto.
Qed.
Theorem source_rec_binary_functional M phi u v a b:
  source_rec_binary M phi u v a ->source_rec_binary M phi u v b ->a=b.
Proof.
  intros(ab&ac&HA&HSubA)(bb&bc&HB&HSubB).
  pose proof(proj1(numerical_substitution_extensional M phi bb bc(code_numeral M 2)ab ac(code_numeral M 2)(code_numeral M 2)b
    (source_pc_reopening_equivalent M v u bb bc ab ac(code_numeral M 2)HB HA))HSubB) as HSubB'.
  exact(numerical_substitution_functional M phi ab ac(code_numeral M 2)(code_numeral M 2)a b HSubA HSubB').
Qed.

Theorem source_rec_binary_from_substitution M phi rb rc rn base out u v:
  source_bounded M phi(code_numeral M 2) ->numerical_substitution M phi rb rc rn base out ->
  substitution_lookup M rb rc rn base(zeroM M)u ->substitution_lookup M rb rc rn base(code_numeral M 1)v ->
  source_rec_binary M phi u v out.
Proof.
  intros HB HS HU HV. destruct(source_role_reopening_total M v u) as(b&c&HM). exists b,c. split;[exact HM|].
  exact(source_two_role_substitution M phi rb rc rn base out u v b c HB HS HU HV HM).
Qed.

Theorem source_rec_binary_bounded M phi u v out k:
  source_bounded M phi(code_numeral M 2) ->coding_lt M u k ->coding_lt M v k ->source_rec_binary M phi u v out ->source_bounded M out k.
Proof.
  intros HB HU HV(b&c&HM&HS).
  apply(numerical_substitution_preserves_bound M phi b c(code_numeral M 2)(code_numeral M 2)out(code_numeral M 2)k HB HS).
  intros i j HI HJ. destruct(source_numeral_initial_segment M 2 i HI) as(n&HN&->).
  pose proof(substitution_lookup_functional M b c(code_numeral M 2)(code_numeral M 2)(code_numeral M n)j
    (if Nat.eqb n 0 then u else v)HJ(source_pc_reopening_lookup M v u b c(code_numeral M 2)n HM HN)) as E.
  subst j. destruct n as[|[|n]];try lia;assumption.
Qed.

Print Assumptions source_rec_binary_total.
Print Assumptions source_rec_binary_functional.
Print Assumptions source_rec_binary_from_substitution.
Print Assumptions source_rec_binary_bounded.
