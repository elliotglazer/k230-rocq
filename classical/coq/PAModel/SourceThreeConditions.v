(** Literal conjunction/currying conversions for three ordinary hypotheses. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  SourcePropositionalTemplates SourceWitnessProofComposition SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition source_three_curried_template :=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)
  (SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTSlot 4)))).
Definition source_three_grouped_template :=SPTImpl(SPTAnd(SPTSlot 0)(SPTAnd(SPTSlot 1)(SPTSlot 2)))
  (SPTImpl(SPTSlot 3)(SPTSlot 4)).

Theorem source_three_uncurry_program :source_prop_program[source_three_curried_template]source_three_grouped_template.
Proof.
  unfold source_three_curried_template,source_three_grouped_template.
  apply SPTII,SPTII. eapply SPTIE.
  - eapply SPTIE.
    + eapply SPTIE.
      * eapply SPTIE.
        -- apply SPTCtx. right;right;now left.
        -- eapply SPTCE1. apply SPTCtx. right;now left.
      * eapply SPTCE1,SPTCE2. apply SPTCtx. right;now left.
    + eapply SPTCE2,SPTCE2. apply SPTCtx. right;now left.
  - apply SPTCtx. now left.
Qed.

Theorem source_three_curry_program :source_prop_program[source_three_grouped_template]source_three_curried_template.
Proof.
  unfold source_three_curried_template,source_three_grouped_template.
  apply SPTII,SPTII,SPTII,SPTII. eapply SPTIE.
  - eapply SPTIE.
    + apply SPTCtx. right;right;right;right;now left.
    + apply SPTCI.
      * apply SPTCtx. right;right;right;now left.
      * apply SPTCI;apply SPTCtx;[right;right;now left|right;now left].
  - apply SPTCtx. now left.
Qed.

Definition source_three_conditions M a b c condition :=exists bc,
  sf_relation M SFAnd b c bc /\sf_relation M SFAnd a bc condition.
Definition source_three_curried M a b c d e law :=exists de cde bcde,
  sf_relation M SFImpl d e de /\sf_relation M SFImpl c de cde /\
  sf_relation M SFImpl b cde bcde /\sf_relation M SFImpl a bcde law.

Theorem source_three_condition_graphs M a b c d e condition grouped law :
  source_three_conditions M a b c condition ->source_three_curried M a b c d e law ->
  (exists de,sf_relation M SFImpl d e de /\sf_relation M SFImpl condition de grouped) ->
  let rho:=fun i=>match i with 0=>a|1=>b|2=>c|3=>d|_=>e end in
  code_relation M rho(source_prop_expression source_three_curried_template) law /\
  code_relation M rho(source_prop_expression source_three_grouped_template) grouped.
Proof.
  intros(bc&HBC&HCond)(de&cde&bcde&HDE&HCDE&HBCDE&HL)(de'&HDE'&HG) rho.
  assert(E:de'=de) by(eapply sf_relation_functional;eassumption). subst de'.
  split;unfold source_three_curried_template,source_three_grouped_template.
  - eapply source_prop_template_join;[reflexivity| |exact HL].
    eapply source_prop_template_join;[reflexivity| |exact HBCDE].
    eapply source_prop_template_join;[reflexivity| |exact HCDE].
    eapply source_prop_template_join;[reflexivity|reflexivity|exact HDE].
  - eapply source_prop_template_join;[| |exact HG].
    + eapply source_prop_template_join;[reflexivity| |exact HCond].
      eapply source_prop_template_join;[reflexivity|reflexivity|exact HBC].
    + eapply source_prop_template_join;[reflexivity|reflexivity|exact HDE].
Qed.

Theorem source_zfr_three_conditions_conversion M a b c d e condition grouped law k :
  source_bounded M a k ->source_bounded M b k ->source_bounded M c k ->source_bounded M d k ->source_bounded M e k ->
  source_three_conditions M a b c condition ->source_three_curried M a b c d e law ->
  (exists de,sf_relation M SFImpl d e de /\sf_relation M SFImpl condition de grouped) ->
  (source_zfr_provable M law <->source_zfr_provable M grouped).
Proof.
  intros HA HB HC HD HE HCond HLaw HGroup.
  pose proof(source_three_condition_graphs M a b c d e condition grouped law HCond HLaw HGroup) as[HL HG].
  set(rho:=fun i:nat=>match i with 0=>a|1=>b|2=>c|3=>d|_=>e end).
  assert(HR:forall i,source_bounded M(rho i) k).
  { intros[|[|[|[|i]]]];assumption. }
  split;intro HP.
  - exact(source_zfr_prop_one M _ _ source_three_uncurry_program rho k law grouped HR HL HG HP).
  - exact(source_zfr_prop_one M _ _ source_three_curry_program rho k grouped law HR HG HL HP).
Qed.

Print Assumptions source_three_uncurry_program.
Print Assumptions source_three_curry_program.
Print Assumptions source_zfr_three_conditions_conversion.
