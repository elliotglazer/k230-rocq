(** Actual source proof of uniqueness from ordinal comparison and the two
    cross exclusions. Predicate instances remain arbitrary internal codes. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalInstantiation NumericalSourceFull SourceInstantiationConstructors
  SourcePropositionalTemplates SourceOrdinalUniquenessProgram.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem source_full_minimal_uniqueness_point M rho k b c n tri lex rex :
  (forall i,source_bounded M (rho i) k) -> context_bounded M b c n k ->
  code_relation M rho (source_prop_expression ordinal_unique_tri) tri ->
  code_relation M rho (source_prop_expression ordinal_unique_left_exclusion) lex ->
  code_relation M rho (source_prop_expression ordinal_unique_right_exclusion) rex ->
  source_full_prv M b c n tri ->source_full_prv M b c n (rho 3) ->
  source_full_prv M b c n (rho 4) ->source_full_prv M b c n lex ->
  source_full_prv M b c n rex ->source_full_prv M b c n (rho 1).
Proof.
  intros HB HC HT HL HR PT PP PQ PL PR.
  apply (source_prop_program_sound M ordinal_unique_premises (SPTSlot 1) ordinal_unique_program
    rho k b c n (rho 1) HB HC);[|reflexivity].
  intros a HA f HF. unfold ordinal_unique_premises in HA.
  destruct HA as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - pose proof (code_relation_functional M _ rho f tri HF HT) as E. now subst f.
  - change (f=rho 3) in HF. now subst f.
  - change (f=rho 4) in HF. now subst f.
  - pose proof (code_relation_functional M _ rho f lex HF HL) as E. now subst f.
  - pose proof (code_relation_functional M _ rho f rex HF HR) as E. now subst f.
Qed.

Theorem source_full_minimal_uniqueness M rho k b c n tri lex rex
    lbody lall rbody rall x y :
  (forall i,source_bounded M (rho i) k) ->context_bounded M b c n k ->
  code_relation M rho (source_prop_expression ordinal_unique_tri) tri ->
  code_relation M rho (source_prop_expression ordinal_unique_left_exclusion) lex ->
  code_relation M rho (source_prop_expression ordinal_unique_right_exclusion) rex ->
  sf_relation M SFAll lbody (zeroM M) lall ->sf_relation M SFAll rbody (zeroM M) rall ->
  numerical_instantiation M lbody x lex ->numerical_instantiation M rbody y rex ->
  source_full_prv M b c n tri ->source_full_prv M b c n (rho 3) ->
  source_full_prv M b c n (rho 4) ->source_full_prv M b c n lall ->
  source_full_prv M b c n rall ->source_full_prv M b c n (rho 1).
Proof.
  intros HB HC HT HL HR HAllL HAllR HIL HIR PT PP PQ PL PR.
  apply (source_full_minimal_uniqueness_point M rho k b c n tri lex rex HB HC HT HL HR PT PP PQ).
  - exact (full_source_AllE M b c n lbody lall x lex
      (source_wf_quantifier_instance M b c n SFAll lbody lall x lex (or_introl eq_refl) HAllL
        (source_full_prv_wellformed M b c n lall PL) HIL) PL HAllL HIL).
  - exact (full_source_AllE M b c n rbody rall y rex
      (source_wf_quantifier_instance M b c n SFAll rbody rall y rex (or_introl eq_refl) HAllR
        (source_full_prv_wellformed M b c n rall PR) HIR) PR HAllR HIR).
Qed.

Print Assumptions source_full_minimal_uniqueness_point.
Print Assumptions source_full_minimal_uniqueness.
