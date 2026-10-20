(** The selector's false branch is supplied by the actual five-axiom
    Foundation derivation, now recognized in the exact ZFR descriptor. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalSourceFull NumericalInstantiation SourceInstantiationConstructors
  ZFCFiniteAxiomTemplates ZFCFiniteSourceCodes NumericalCoreAxioms NumericalZFRAxioms
  SourceNumeralLift FiniteSourceNoSelf SourceZFCNoSelf SourceZFRProvability.
From Undecidability.FOL Require Import Sets.minZF.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem source_zfr_no_self_closed M :source_zfr_provable M
  (code_numeral M (sf_make SFAll (sf_make SFImpl (sf_make SFMember 0 0) 0) 0)).
Proof.
  destruct (source_model_context_total M finite_no_self_axioms) as (b&c&n&HC).
  exists b,c,n. split.
  - intros f HF. apply (proj1 (source_model_context_member_iff M b c n finite_no_self_axioms f HC)) in HF.
    destruct HF as (phi&HP&->). unfold finite_no_self_axioms in HP.
    destruct HP as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + right. exact (source_formula_numeral_graph M (zfc_fixed_source ZFCFoundation)).
    + left;left. exists ZFCPair. split;[cbn [zfc_core_fixed_tags List.In];tauto|].
      exact (source_formula_numeral_graph M (zfc_fixed_source ZFCPair)).
    + left;left. exists ZFCRefl. split;[cbn [zfc_core_fixed_tags List.In];tauto|].
      exact (source_formula_numeral_graph M (zfc_fixed_source ZFCRefl)).
    + left;left. exists ZFCSym. split;[cbn [zfc_core_fixed_tags List.In];tauto|].
      exact (source_formula_numeral_graph M (zfc_fixed_source ZFCSym)).
    + left;left. exists ZFCEqElem. split;[cbn [zfc_core_fixed_tags List.In];tauto|].
      exact (source_formula_numeral_graph M (zfc_fixed_source ZFCEqElem)).
  - exact (source_full_forward_model M finite_no_self_axioms _ finite_no_self_closed b c n HC).
Qed.

Theorem source_zfr_no_self M x atom neg :
  sf_relation M SFMember x x atom ->sf_relation M SFImpl atom (zeroM M) neg ->
  source_zfr_provable M neg.
Proof.
  intros HA HN.
  set (atom0:=code_numeral M (sf_make SFMember 0 0)).
  set (neg0:=code_numeral M (sf_make SFImpl (sf_make SFMember 0 0) 0)).
  set (ax:=code_numeral M (sf_make SFAll (sf_make SFImpl (sf_make SFMember 0 0) 0) 0)).
  destruct (source_zfr_no_self_closed M) as (b&c&n&HC&HP).
  pose proof (sf_make_numeral M SFAll (sf_make SFImpl (sf_make SFMember 0 0) 0) 0) as HAll.
  pose proof (source_instantiation_negative_diagonal M atom0 neg0 x atom neg
    (sf_make_numeral M SFMember 0 0)
    (sf_make_numeral M SFImpl (sf_make SFMember 0 0) 0) HA HN) as HI.
  exists b,c,n. split;[exact HC|].
  apply (full_source_AllE M b c n neg0 ax x neg);[|exact HP|exact HAll|exact HI].
  exact (source_wf_quantifier_instance M b c n SFAll neg0 ax x neg (or_introl eq_refl)
    HAll (source_full_prv_wellformed M b c n ax HP) HI).
Qed.

Print Assumptions source_zfr_no_self_closed.
Print Assumptions source_zfr_no_self.
