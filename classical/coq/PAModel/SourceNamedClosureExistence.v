(** A genuine source-proof transport into the shared named witness frame.
    It applies to An, NumF, and any internally coded matrix bounded by2. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift
 SourceFiniteParameters SourceFiniteNameParameters SourceNamedFiniteCalibration SourceNamedDifferenceCertificates
 SourceRepresentationClosureRecipe SourceDefinabilityPrimitives NumericalRenamingMaps NumericalRenaming FixedSourceBounds
 SourceEnvironmentCarrierClosure SourceRepresentationFalsityClosure SourceNamedClosureExistsRenaming
 SourceRepresentativeRenaming SourceNamedQuantifierRules SourcePropositionalTemplates SourcePropRenaming
 SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors SourceZFRProvability.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From Stdlib Require Import Lia Arith.PeanoNat.
Open Scope minZFsyn.
Unset Implicit Arguments.

Definition NCE_coordinate_name i:=match i with 0=>1|1=>7|_=>i end.
Definition NCE_coordinate_substitution i:sf_term:=$(NCE_coordinate_name i).
Lemma NCE_coordinate_tail i:(3<=i)%nat ->NCE_coordinate_name i=i.
Proof. intro H. destruct i as[|[|i]];try lia;reflexivity. Qed.
Lemma NCE_coordinate_successor:source_def_successor01[NCE_coordinate_substitution]=named_difference_successor.
Proof. reflexivity. Qed.
Lemma NCE_coordinate_closure:representation_closure_condition[NCE_coordinate_substitution]=named_difference_closure.
Proof. reflexivity. Qed.
Theorem source_named_closure_coordinates_total M:exists b c,
 renaming_lookup M b c(code_numeral M 3)(zeroM M)(zeroM M)(code_numeral M 1) /\
 renaming_lookup M b c(code_numeral M 3)(zeroM M)(code_numeral M 1)(code_numeral M 7) /\
 renaming_lookup M b c(code_numeral M 3)(zeroM M)(code_numeral M 2)(code_numeral M 2) /\
 numerical_renaming M(code_numeral M(sf_encode source_def_successor01))b c(code_numeral M 3)(zeroM M)
  (code_numeral M(sf_encode named_difference_successor)) /\
 numerical_renaming M(code_numeral M(sf_encode representation_closure_condition))b c(code_numeral M 3)(zeroM M)
  (code_numeral M(sf_encode named_difference_closure)).
Proof.
 destruct(source_finite_names_total M 3(fun i=>code_numeral M(NCE_coordinate_name i))(zeroM M))as(b&c&HNames).
 assert(HMap:forall i v,code_relation M(fun _=>zeroM M)(CEconst(NCE_coordinate_name i))v ->
   renaming_lookup M b c(code_numeral M 3)(zeroM M)(code_numeral M i)v).
 { intros i v HV. change(v=code_numeral M(NCE_coordinate_name i))in HV. subst v.
   destruct(Nat.lt_ge_cases i 3)as[HI|HI];[exact(HNames i HI)|].
   rewrite(NCE_coordinate_tail i HI).
   apply(proj2(renaming_lookup_outside M b c(code_numeral M 3)(zeroM M)(code_numeral M i)(code_numeral M i)
    ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M i 3))in H;lia))).
   symmetry. apply coding_add_zero_r. }
 exists b,c. split;[exact(HNames 0 ltac:(lia))|]. split;[exact(HNames 1 ltac:(lia))|].
 split;[exact(HNames 2 ltac:(lia))|]. split.
 - apply(source_finite_parameter_renaming M source_def_successor01(fun i=>CEconst(NCE_coordinate_name i))
    (fun _=>zeroM M)b c(code_numeral M 3)(zeroM M)_ HMap).
   rewrite <-NCE_coordinate_successor.
   exact(source_parameter_substitution_calibration M source_def_successor01 NCE_coordinate_substitution).
 - apply(source_finite_parameter_renaming M representation_closure_condition(fun i=>CEconst(NCE_coordinate_name i))
    (fun _=>zeroM M)b c(code_numeral M 3)(zeroM M)_ HMap).
   rewrite <-NCE_coordinate_closure.
   exact(source_parameter_substitution_calibration M representation_closure_condition NCE_coordinate_substitution).
Qed.

Definition NCE_template:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)).
Definition NCE_values M succ closure ex i:=match i with 0=>succ|1=>closure|2=>ex|_=>zeroM M end.
Definition named_closure_values M ex:=NCE_values M(code_numeral M(sf_encode named_difference_successor))
 (code_numeral M(sf_encode named_difference_closure))ex.

Theorem source_zfr_named_closure_existence M rep canonical r named member body ex out:
 source_bounded M rep(code_numeral M 2) ->
 source_environment_carrier_closure_statement M rep canonical ->source_zfr_provable M canonical ->
 ~coding_lt M r(code_numeral M 3) ->source_representative_renaming M r rep named ->
 sf_relation M SFMember r(code_numeral M 2)member ->sf_relation M SFAnd member named body ->
 source_named_quantifier M false r body ex ->
 code_relation M(named_closure_values M ex)(source_prop_expression NCE_template)out ->source_zfr_provable M out.
Proof.
 intros BRep HCanonical PCanonical HR HNamed HMember HBody HEx HOut.
 destruct(sf_relation_total M SFAnd(representation_member_code M)rep)as(cbody&HCB).
 destruct(sf_relation_total M SFEx cbody(zeroM M))as(cex&HCE).
 destruct(sf_relation_total M SFImpl(code_numeral M(sf_encode representation_closure_condition))cex)as(cmiddle&HCM).
 destruct(sf_relation_total M SFImpl(code_numeral M(sf_encode source_def_successor01))cmiddle)as(cout&HCO).
 pose proof(source_environment_carrier_closure_statement_join M rep cbody cex cmiddle cout HCB HCE HCM HCO)as HJoin.
 assert(E:canonical=cout)by(eapply source_environment_carrier_closure_statement_functional;eassumption). subst cout.
 destruct(source_named_closure_coordinates_total M)as(b&c&HZero&HOne&HTwo&HS&HC).
 pose proof(source_auxiliary_representation_exists_forward M rep named r member body ex cbody cex b c(code_numeral M 3)(zeroM M)
  BRep HR HNamed HMember HBody HEx HZero HTwo HCB HCE)as HExRename.
 set(cvalues:=NCE_values M(code_numeral M(sf_encode source_def_successor01))
  (code_numeral M(sf_encode representation_closure_condition))cex).
 assert(GCanonical:code_relation M cvalues(source_prop_expression NCE_template)canonical).
 { unfold NCE_template. apply(source_prop_template_join M cvalues SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2))
    (code_numeral M(sf_encode source_def_successor01))cmiddle canonical eq_refl);[|exact HCO].
   exact(source_prop_template_join M cvalues SFImpl(SPTSlot 1)(SPTSlot 2)
    (code_numeral M(sf_encode representation_closure_condition))cex cmiddle eq_refl eq_refl HCM). }
 assert(HRename:numerical_renaming M canonical b c(code_numeral M 3)(zeroM M)out).
 { apply(source_prop_renaming M cvalues(named_closure_values M ex)b c(code_numeral M 3)(zeroM M)
    NCE_template canonical out);[|exact GCanonical|exact HOut].
   cbn[source_prop_slots NCE_template cvalues NCE_values named_closure_values].
   exact(conj HS(conj HC HExRename)). }
 apply(proj1(source_zfr_descriptor_provable M out)).
 exact(source_descriptor_provable_renaming M ZFRSourceDescriptor canonical b c(code_numeral M 3)(zeroM M)out
  (proj2(source_zfr_descriptor_provable M canonical)PCanonical)HRename).
Qed.
Print Assumptions source_named_closure_coordinates_total.
Print Assumptions source_zfr_named_closure_existence.
