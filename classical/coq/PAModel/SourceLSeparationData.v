(** Literal syntax used at the final z-point of L Separation. The
    reflection input is an ordinary forall source formula with actual
    class/set relativizations of the same arbitrary internal body. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded SourceRelativization SourceRelativizationBounds SourceSetRelativization
  SourceSetRelativizationBounds NumericalContexts NumericalSourceFull
  SourcePropositionalTemplates SourceLSeparationPoint SourceLSeparationProfile.
Unset Implicit Arguments.

Definition source_lsep_environment M zx zy za lp sp i :=
  match i with 0=>zx|1=>zy|2=>za|3=>lp|4=>sp|_=>zeroM M end.
Definition source_lsep_data M domain body carrier zx zy za lp sp :=
  sf_relation M SFMember (zeroM M)(code_numeral M 1) zx /\
  sf_relation M SFMember (zeroM M) carrier zy /\
  sf_relation M SFMember (zeroM M)(code_numeral M 2) za /\
  source_relativization M domain body lp /\source_set_relativization M carrier body sp.

Theorem source_lsep_data_total M domain body carrier :
  exists zx zy za lp sp,source_lsep_data M domain body carrier zx zy za lp sp.
Proof.
  destruct (sf_relation_total M SFMember (zeroM M)(code_numeral M 1)) as [zx HX].
  destruct (sf_relation_total M SFMember (zeroM M) carrier) as [zy HY].
  destruct (sf_relation_total M SFMember (zeroM M)(code_numeral M 2)) as [za HA].
  destruct (source_relativization_total M domain body) as [lp HL].
  destruct (source_set_relativization_total M carrier body) as [sp HS].
  exists zx,zy,za,lp,sp. repeat first [assumption|split].
Qed.

Lemma source_lsep_data_bound M domain body carrier zx zy za lp sp k :
  source_bounded M domain (code_numeral M 1) ->source_bounded M body (succM M k) ->
  coding_lt M (code_numeral M 2)(succM M k) ->coding_lt M carrier (succM M k) ->
  source_lsep_data M domain body carrier zx zy za lp sp ->
  forall i,source_bounded M (source_lsep_environment M zx zy za lp sp i) (succM M k).
Proof.
  intros HD HB H2 HY (HX&HZY&HA&HL&HS) i.
  assert (H1:coding_lt M (code_numeral M 1)(succM M k)).
  { exact (coding_lt_trans M (code_numeral M 1)(code_numeral M 2)(succM M k)
      (coding_lt_succ M (code_numeral M 1)) H2). }
  destruct i as [|[|[|[|[|i]]]]];cbn [source_lsep_environment].
  - apply (proj2 (source_bounded_accept_atom M SFMember (zeroM M)(code_numeral M 1) zx
      (succM M k)(or_introl eq_refl) HX)). split;[apply coding_zero_lt_succ|exact H1].
  - apply (proj2 (source_bounded_accept_atom M SFMember (zeroM M) carrier zy
      (succM M k)(or_introl eq_refl) HZY)). split;[apply coding_zero_lt_succ|exact HY].
  - apply (proj2 (source_bounded_accept_atom M SFMember (zeroM M)(code_numeral M 2) za
      (succM M k)(or_introl eq_refl) HA)). split;[apply coding_zero_lt_succ|exact H2].
  - exact (source_relativization_preserves_bound M body domain (succM M k) lp HD HB HL).
  - exact (source_set_relativization_preserves_bound M body carrier (succM M k) sp HY HB HS).
  - apply source_bounded_accept_falsity.
Qed.

Theorem source_full_L_separation_profile_from_data M domain body carrier zx zy za lp sp k b c n
    definition reflection transitive result alld allr allt allresult guarded guardedall :
  source_bounded M domain (code_numeral M 1) ->source_bounded M body (succM M k) ->
  coding_lt M (code_numeral M 2)(succM M k) ->coding_lt M carrier (succM M k) ->
  source_lsep_data M domain body carrier zx zy za lp sp ->context_bounded M b c n k ->
  code_relation M (source_lsep_environment M zx zy za lp sp)
    (source_prop_expression lsep_definition_point) definition ->
  code_relation M (source_lsep_environment M zx zy za lp sp)
    (source_prop_expression lsep_reflection_point) reflection ->
  code_relation M (source_lsep_environment M zx zy za lp sp)
    (source_prop_expression lsep_transitive_point) transitive ->
  code_relation M (source_lsep_environment M zx zy za lp sp)
    (source_prop_expression lsep_result_point) result ->
  sf_relation M SFAll definition (zeroM M) alld ->sf_relation M SFAll reflection (zeroM M) allr ->
  sf_relation M SFAll transitive (zeroM M) allt ->sf_relation M SFAll result (zeroM M) allresult ->
  sf_relation M SFImpl domain result guarded ->sf_relation M SFAll guarded (zeroM M) guardedall ->
  source_full_prv M b c n alld ->source_full_prv M b c n allr ->source_full_prv M b c n allt ->
  source_full_prv M b c n guardedall.
Proof.
  intros HD HB H2 HY HData HC HDef HRef HT HG HAD HAR HAT HAG HI HGA PD PR PT.
  exact (source_full_L_separation_guarded_profile M domain (source_lsep_environment M zx zy za lp sp)
    k b c n definition reflection transitive result alld allr allt allresult guarded guardedall
    HD (source_lsep_data_bound M domain body carrier zx zy za lp sp k HD HB H2 HY HData)
    HC HDef HRef HT HG HAD HAR HAT HAG HI HGA PD PR PT).
Qed.

Print Assumptions source_lsep_data_total.
Print Assumptions source_lsep_data_bound.
Print Assumptions source_full_L_separation_profile_from_data.
