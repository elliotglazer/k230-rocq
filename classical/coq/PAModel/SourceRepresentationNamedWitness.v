(** Literal representative witnesses, including their sharp free-name
    bound after the auxiliary representative is existentially closed. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SourceNumeralLift FixedSourceBounds NumericalRenamingMaps NumericalRenaming SourceRepresentativeRenaming
 SourceRepresentativeQuantifier SourceNamedQuantifierRules.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition representation_named_member02 M :=code_numeral M(sf_make SFMember 0 2).

Theorem source_representative_witness_body_renaming M r rep named member original target :
 source_representative_renaming M r rep named ->sf_relation M SFMember r(code_numeral M 2)member ->
 sf_relation M SFAnd(representation_named_member02 M)rep original ->
 sf_relation M SFAnd member named target ->source_representative_renaming M r original target.
Proof.
 intros HRep HMember HOriginal HTarget.
 apply(proj2(numerical_renaming_binary M SFAnd(representation_named_member02 M)rep original
  r r(code_numeral M 1)(zeroM M)target(or_introl eq_refl)HOriginal)).
 exists member,named. split;[|now split].
 apply(proj2(numerical_renaming_member M(zeroM M)(code_numeral M 2)(representation_named_member02 M)
  r r(code_numeral M 1)(zeroM M)member(sf_make_numeral M SFMember 0 2))).
 exists r,(code_numeral M 2). split;[apply representative_lookup_zero|].
 split;[apply representative_lookup_nonzero|exact HMember].
 intro E. exact(Model.zero_ne_succ M(code_numeral M 1)(eq_sym E)).
Qed.

Theorem source_representation_witness_body_bound M rep body :
 source_bounded M rep(code_numeral M 2) ->
 sf_relation M SFAnd(representation_named_member02 M)rep body ->source_bounded M body(code_numeral M 3).
Proof.
 intros HRep HBody.
 apply(proj2(source_bounded_accept_binary M SFAnd(representation_named_member02 M)rep body
  (code_numeral M 3)(or_introl eq_refl)HBody)). split.
 - apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 2)
    (representation_named_member02 M)(code_numeral M 3)(or_introl eq_refl)(sf_make_numeral M SFMember 0 2))).
   split;[apply coding_zero_lt_succ|apply coding_lt_succ].
 - exact(source_bounded_monotone M rep(code_numeral M 2)(code_numeral M 3)HRep
    (proj2(fixed_source_numeral_lt_iff M 2 4)ltac:(lia))).
Qed.

Theorem source_representation_named_witness_bound M r rep named member original target quantified :
 source_bounded M rep(code_numeral M 2) ->~coding_lt M r(code_numeral M 3) ->
 source_representative_renaming M r rep named ->sf_relation M SFMember r(code_numeral M 2)member ->
 sf_relation M SFAnd(representation_named_member02 M)rep original ->sf_relation M SFAnd member named target ->
 source_named_quantifier M false r target quantified ->source_bounded M quantified(code_numeral M 3).
Proof.
 intros HRep HR HNamed HMember HOriginal HTarget HQ.
 exact(source_representative_quantifier_bound M false original target r(code_numeral M 3)quantified
  (source_representation_witness_body_bound M rep original HRep HOriginal) HR
  (source_representative_witness_body_renaming M r rep named member original target HNamed HMember HOriginal HTarget)HQ).
Qed.

Print Assumptions source_representative_witness_body_renaming.
Print Assumptions source_representation_witness_body_bound.
Print Assumptions source_representation_named_witness_bound.
