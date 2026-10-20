(** Substitution and a fixed schema-map calibration for binary instances. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SourceBounded SourceNumeralLift
 NumericalSubstitutionMaps NumericalSubstitution SourceSubstitutionComposition SourceRoleReopening SourcePieceClosure
 SourcePieceClosureFacts SourceRecursionBinaryInstance SchemaRenamingDescriptors RenamingSubstitution.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_rec_binary_substitution M phi u v out rb rc rn base out' u' v':
 source_bounded M phi(code_numeral M 2) ->source_rec_binary M phi u v out ->
 numerical_substitution M out rb rc rn base out' ->substitution_lookup M rb rc rn base u u' ->
 substitution_lookup M rb rc rn base v v' ->source_rec_binary M phi u' v' out'.
Proof.
 intros BP(ab&ac&HR&HSub)HS HU HV.
 destruct(source_role_reopening_total M v' u')as(bb&bc&HT).
 exists bb,bc. split;[exact HT|].
 apply(numerical_substitution_composition M phi(code_numeral M 2)
  ab ac(code_numeral M 2)(code_numeral M 2)rb rc rn base bb bc(code_numeral M 2)(code_numeral M 2)out out' BP HSub HS).
 intros i j w HI HFirst HSecond.
 destruct(source_numeral_initial_segment M 2 i HI)as(n&HN&->).
 pose proof(substitution_lookup_functional M _ _ _ _ _ j(if Nat.eqb n 0 then u else v)
  HFirst(source_pc_reopening_lookup M v u ab ac(code_numeral M 2)n HR HN))as EJ. subst j.
 assert(EW:w=if Nat.eqb n 0 then u' else v').
 { destruct n as[|[|n]];try lia;eapply substitution_lookup_functional;[exact HSecond|exact HU|exact HSecond|exact HV]. }
 subst w. exact(source_pc_reopening_lookup M v' u' bb bc(code_numeral M 2)n HT HN).
Qed.

Theorem source_rec_binary_rep M phi body s:
 (s=RepA \/s=RepB) ->source_bounded M phi(code_numeral M 2) ->schema_renaming M s phi body ->
 source_rec_binary M phi(code_numeral M 2)(code_numeral M(schema_second s))body.
Proof.
 intros HH BP HR. unfold schema_renaming in HR.
 apply(source_rec_binary_from_substitution M phi _ _ _ _ body(code_numeral M 2)(code_numeral M(schema_second s))BP
  (proj1(numerical_renaming_substitution M phi _ _ _ _ body)HR)).
 - apply(proj1(renaming_substitution_lookup M _ _ _ _ _ _)).
   change(schema_lookup M s(zeroM M)(code_numeral M 2)).
   apply schema_lookup_first. destruct HH as[EH|EH];subst s;reflexivity.
 - apply(proj1(renaming_substitution_lookup M _ _ _ _ _ _)).
   change(schema_lookup M s(code_numeral M 1)(code_numeral M(schema_second s))).
   apply schema_lookup_second. reflexivity.
Qed.
Print Assumptions source_rec_binary_substitution.
Print Assumptions source_rec_binary_rep.
