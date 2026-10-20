(** The two predecessor existential witnesses survive actual source substitution. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution SourceRecursionBinaryInstance SourceRecursionBinaryGraphTransport
 SourceRecursionPrimitiveRelations SourceRecursionPrimitiveTransport SourceRecursionAttemptStepShell.
Unset Implicit Arguments.
Theorem source_rec_transition_witness_substitution M phi f u v out f' u' v' out' rb rc rn base:
 source_bounded M phi(code_numeral M 2) ->source_rec_transition_witness M phi f u v out ->
 source_rec_transition_witness M phi f' u' v' out' ->
 substitution_lookup M rb rc rn base f f' ->substitution_lookup M rb rc rn base u u' ->substitution_lookup M rb rc rn base v v' ->
 numerical_substitution M out rb rc rn base out'.
Proof.
 intros BP(app&binary&body&HA&HG&HB&HE)(app'&binary'&body'&HA'&HG'&HB'&HE')HF HU HV.
 destruct(substitution_lift_total M rb rc rn base)as(lb&lc&ln&HL).
 pose proof(source_rec_app_substitution M(succM M f)(succM M u)(zeroM M)app
  (succM M f')(succM M u')(zeroM M)app' lb lc ln(succM M base)HA HA'
  (proj2(proj2 HL)f f' HF)(proj2(proj2 HL)u u' HU)(proj1(proj2 HL)))as HApp.
 pose proof(source_rec_binary_substitution_graph M phi(zeroM M)(succM M v)binary(zeroM M)(succM M v')binary' lb lc ln(succM M base)
  BP HG HG'(proj1(proj2 HL))(proj2(proj2 HL)v v' HV))as HBinary.
 assert(HBody:numerical_substitution M body lb lc ln(succM M base)body').
 { apply(proj2(numerical_substitution_binary M SFAnd app binary body lb lc ln(succM M base)body'(or_introl eq_refl)HB)).
   exists app',binary'. auto. }
 apply(proj2(numerical_substitution_quantifier M false body out rb rc rn base out' HE)).
 exists lb,lc,ln,body'. auto.
Qed.
Print Assumptions source_rec_transition_witness_substitution.
