(** Lift the checked L-Separation point program under a literal forall,
    then add the exact L guard without changing its witness or predicate. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalContextRenaming NumericalSourceFull
  SourceQuantifierRules SourceUniversalPropositional SourceUniversalGuard
  SourcePropositionalTemplates SourceLSeparationPoint.
Unset Implicit Arguments.

Theorem source_full_L_separation_profile M rho k b c n definition reflection transitive result
    alld allr allt allresult :
  (forall i,source_bounded M (rho i) (succM M k)) ->context_bounded M b c n k ->
  code_relation M rho (source_prop_expression lsep_definition_point) definition ->
  code_relation M rho (source_prop_expression lsep_reflection_point) reflection ->
  code_relation M rho (source_prop_expression lsep_transitive_point) transitive ->
  code_relation M rho (source_prop_expression lsep_result_point) result ->
  sf_relation M SFAll definition (zeroM M) alld ->sf_relation M SFAll reflection (zeroM M) allr ->
  sf_relation M SFAll transitive (zeroM M) allt ->sf_relation M SFAll result (zeroM M) allresult ->
  source_full_prv M b c n alld ->source_full_prv M b c n allr ->source_full_prv M b c n allt ->
  source_full_prv M b c n allresult.
Proof.
  intros HB HC HD HR HT HG HAD HAR HAT HAG PD PR PT.
  destruct (context_shift_total M b c n) as [u [v HS]].
  apply (full_source_AllI M b c n result allresult u v);[| |exact HS|exact HAG].
  - exists k. split;[|exact HC].
    apply (proj2 (source_bounded_accept_unary M SFAll result allresult k (or_introl eq_refl) HAG)).
    exact (source_prop_template_bound M rho lsep_result_point (succM M k) HB result HG).
  - apply (source_full_L_separation_point M rho (succM M k) u v n definition reflection transitive result
      HB (context_shift_preserves_bound M b c n u v k HS HC) HD HR HT HG).
    + exact (source_full_all_shift M b c n definition alld u v HAD PD HS).
    + exact (source_full_all_shift M b c n reflection allr u v HAR PR HS).
    + exact (source_full_all_shift M b c n transitive allt u v HAT PT HS).
Qed.

Theorem source_full_L_separation_guarded_profile M domain rho k b c n definition reflection transitive result
    alld allr allt allresult guarded guardedall :
  source_bounded M domain (code_numeral M 1) ->
  (forall i,source_bounded M (rho i) (succM M k)) ->context_bounded M b c n k ->
  code_relation M rho (source_prop_expression lsep_definition_point) definition ->
  code_relation M rho (source_prop_expression lsep_reflection_point) reflection ->
  code_relation M rho (source_prop_expression lsep_transitive_point) transitive ->
  code_relation M rho (source_prop_expression lsep_result_point) result ->
  sf_relation M SFAll definition (zeroM M) alld ->sf_relation M SFAll reflection (zeroM M) allr ->
  sf_relation M SFAll transitive (zeroM M) allt ->sf_relation M SFAll result (zeroM M) allresult ->
  sf_relation M SFImpl domain result guarded ->sf_relation M SFAll guarded (zeroM M) guardedall ->
  source_full_prv M b c n alld ->source_full_prv M b c n allr ->source_full_prv M b c n allt ->
  source_full_prv M b c n guardedall.
Proof.
  intros HDb HB HC HD HR HT HG HAD HAR HAT HAG HI HGA PD PR PT.
  apply (source_full_universal_guard M domain b c n result allresult guarded guardedall HDb HAG HI HGA).
  exact (source_full_L_separation_profile M rho k b c n definition reflection transitive result
    alld allr allt allresult HB HC HD HR HT HG HAD HAR HAT HAG PD PR PT).
Qed.

Print Assumptions source_full_L_separation_profile.
Print Assumptions source_full_L_separation_guarded_profile.
