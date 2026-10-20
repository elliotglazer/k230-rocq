(** The source image of raw code1 is membership(0,0), not source falsity.
    Foundation supplies the actual proof that this image implies falsity. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent CodeTags Pairing
  SetFormulaCodes SetCodeDescent NumericalContexts NumericalSourceFull
  ZFCFiniteAxiomTemplates ZFCFiniteSourceCodes NumericalZFCAxioms SourceNumeralLift
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation
  SourceZFCProvability SourceZFCBasicClosure SourceZFCInstantiation
  RawSourceImage RawSourceImageInversion FiniteSourceNoSelf.
From Undecidability.FOL Require Import Sets.minZF.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem source_zfc_no_self_closed M : source_zfc_provable M
  (code_numeral M (sf_make SFAll (sf_make SFImpl (sf_make SFMember 0 0) 0) 0)).
Proof.
  destruct (source_model_context_total M finite_no_self_axioms) as (b&c&n&HC).
  exists b,c,n. split.
  - intros f HF. apply (proj1 (source_model_context_member_iff M b c n finite_no_self_axioms f HC)) in HF.
    destruct HF as (phi&HP&->). unfold finite_no_self_axioms in HP.
    destruct HP as [<-|[<-|[<-|[<-|[<-|[]]]]]];left.
    + exists ZFCFoundation. exact (source_formula_numeral_graph M (zfc_fixed_source ZFCFoundation)).
    + exists ZFCPair. exact (source_formula_numeral_graph M (zfc_fixed_source ZFCPair)).
    + exists ZFCRefl. exact (source_formula_numeral_graph M (zfc_fixed_source ZFCRefl)).
    + exists ZFCSym. exact (source_formula_numeral_graph M (zfc_fixed_source ZFCSym)).
    + exists ZFCEqElem. exact (source_formula_numeral_graph M (zfc_fixed_source ZFCEqElem)).
  - exact (source_full_forward_model M finite_no_self_axioms _ finite_no_self_closed b c n HC).
Qed.

Theorem source_instantiation_negative_diagonal M atom0 neg0 x atomx negx :
  sf_relation M SFMember (zeroM M) (zeroM M) atom0 ->
  sf_relation M SFImpl atom0 (zeroM M) neg0 ->
  sf_relation M SFMember x x atomx -> sf_relation M SFImpl atomx (zeroM M) negx ->
  numerical_instantiation M neg0 x negx.
Proof.
  intros H0 HN0 HX HNX. destruct (substitution_singleton_total M x) as (b&c&HB&_).
  exists b,c. split;[exact HB|].
  apply (proj2 (numerical_substitution_binary M SFImpl atom0 (zeroM M) neg0 b c
    (succM M (zeroM M)) (zeroM M) negx ltac:(unfold sf_binary;auto) HN0)).
  exists atomx,(zeroM M). split.
  - apply (proj2 (numerical_substitution_member M (zeroM M) (zeroM M) atom0 b c
      (succM M (zeroM M)) (zeroM M) atomx H0)). exists x,x. auto.
  - split;[|exact HNX]. apply (proj2 (numerical_substitution_invalid M (zeroM M) b c
      (succM M (zeroM M)) (zeroM M) (zeroM M) (or_introl eq_refl))). reflexivity.
Qed.

Theorem source_zfc_no_self M x atomx negx :
  sf_relation M SFMember x x atomx -> sf_relation M SFImpl atomx (zeroM M) negx ->
  source_zfc_provable M negx.
Proof.
  intros HX HNX.
  set (atom0:=code_numeral M (sf_make SFMember 0 0)).
  set (neg0:=code_numeral M (sf_make SFImpl (sf_make SFMember 0 0) 0)).
  set (ax:=code_numeral M (sf_make SFAll (sf_make SFImpl (sf_make SFMember 0 0) 0) 0)).
  apply (source_zfc_provable_all_elim M neg0 ax x negx (source_zfc_no_self_closed M)).
  - exact (sf_make_numeral M SFAll (sf_make SFImpl (sf_make SFMember 0 0) 0) 0).
  - apply (source_instantiation_negative_diagonal M atom0 neg0 x atomx negx).
    + exact (sf_make_numeral M SFMember 0 0).
    + exact (sf_make_numeral M SFImpl (sf_make SFMember 0 0) 0).
    + exact HX.
    + exact HNX.
Qed.

Theorem raw_one_source_member M s : raw_source_image M (code_numeral M 1) s ->
  sf_relation M SFMember (zeroM M) (zeroM M) s.
Proof.
  intro HS. apply (raw_source_member_inv M (zeroM M) (zeroM M) (code_numeral M 1) s);[|exact HS].
  exists (zeroM M). split;[apply pair_zero|].
  rewrite Arithmetic.mul_comm,Arithmetic.mul_zero,coding_add_zero. reflexivity.
Qed.

Theorem source_zfc_raw_one_refutes M s :
  raw_source_image M (code_numeral M 1) s -> source_zfc_provable M s ->
  source_zfc_provable M (zeroM M).
Proof.
  intros HS HP. destruct (sf_relation_total M SFImpl s (zeroM M)) as [neg Hneg].
  exact (source_zfc_provable_mp M s (zeroM M) neg HP
    (source_zfc_no_self M (zeroM M) s neg (raw_one_source_member M s HS) Hneg) Hneg).
Qed.

Print Assumptions source_zfc_no_self_closed.
Print Assumptions source_zfc_no_self.
Print Assumptions source_zfc_raw_one_refutes.
