(** Literal range, covering-level and cut-output shells. These finite
    shells preserve the same arbitrary internal image matrix. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SetSchemaConstructors
 SourceFiniteCutoffShift SourceQfFunctionality SourceCutoffShiftConstructors SourceCutoffQuantifiers SourceCutoffPropositional
 SourcePropositionalRebase SourceWFSeparationConstructor SourceWFSeparationWitness SourceLSeparationWitnessShift SourceLDefinableProfile SourceWFReplacementProfileGraphs SourceQuantifierRules.
Unset Implicit Arguments.
Definition E_L_range_profile d theta (z:nat):=E_sf_all(E_sf SFImpl d(E_sf_iff(E_sf_mem 0 z)theta)).
Definition E_L_cover_profile d:=E_sf_all(E_sf SFImpl(E_sf_mem 0 2)(E_sf SFImpl d(E_sf_mem 0 1))).
Definition E_L_cover_witness d:=E_sf_ex(E_sf SFAnd d(E_L_cover_profile d)).
Definition E_L_cut_witness d theta:=E_sf_ex(E_sf SFAnd d(E_L_range_profile d theta 1)).
Definition E_L_selection_witness d theta:=E_sf_ex(E_sf SFAnd d
 (E_sf_all(E_sf SFImpl d(E_sf_iff(E_sf_mem 0 1)(E_sf SFAnd(E_sf_mem 0 2)theta))))).

Theorem source_L_range_profile_cutoff M depth domain theta other z a b:
 source_bounded M domain(code_numeral M 1) ->source_cutoff_shift M(S depth)theta other ->
 code_relation M(schema_env3 domain theta(zeroM M))(E_L_range_profile(CEvar 0)(CEvar 1)z)a ->
 code_relation M(schema_env3 domain other(zeroM M))
   (E_L_range_profile(CEvar 0)(CEvar 1)(sf_index(source_shift_sigma(S depth)z)))b ->
 source_cutoff_shift M depth a b.
Proof.
 intros HD HT HA HB.
 unfold E_L_range_profile,E_sf_all in HA,HB.
 destruct(schema_expression_quantifier_split M _ SFAll _ a HA)as(p&HPA&HAllA).
 destruct(schema_expression_quantifier_split M _ SFAll _ b HB)as(q&HPB&HAllB).
 destruct(schema_expression_split M _ SFImpl _ _ p HPA)as(d&ia&HDa&HIa&HImpA).
 destruct(schema_expression_split M _ SFImpl _ _ q HPB)as(d'&ib&HDb&HIb&HImpB).
 change(d=domain)in HDa. change(d'=domain)in HDb. subst d d'.
 destruct(code_relation_total M(E_sf_mem 0 z)(schema_env3 domain theta(zeroM M)))as(ma&HMA).
 destruct(code_relation_total M(E_sf_mem 0(sf_index(source_shift_sigma(S depth)z)))
  (schema_env3 domain other(zeroM M)))as(mb&HMB).
 destruct(schema_iff_split M(schema_env3 domain theta(zeroM M))(E_sf_mem 0 z)(CEvar 1)ma theta ia HMA eq_refl HIa)as(fa&ra&HFA&HRA&HIA).
 destruct(schema_iff_split M(schema_env3 domain other(zeroM M))(E_sf_mem 0(sf_index(source_shift_sigma(S depth)z)))(CEvar 1)mb other ib HMB eq_refl HIb)as(fb&rb&HFB&HRB&HIB).
 pose proof(source_cutoff_shift_fixed_member M(S depth)0 z ma mb HMA HMB)as HM.
 assert(HF:source_cutoff_shift M(S depth)fa fb).
 { eapply source_cutoff_shift_binary;[right;right;reflexivity|exact HFA|exact HFB|exact HM|exact HT]. }
 assert(HR:source_cutoff_shift M(S depth)ra rb).
 { eapply source_cutoff_shift_binary;[right;right;reflexivity|exact HRA|exact HRB|exact HT|exact HM]. }
 assert(HI:source_cutoff_shift M(S depth)ia ib).
 { eapply source_cutoff_shift_binary;[left;reflexivity|exact HIA|exact HIB|exact HF|exact HR]. }
 apply(source_cutoff_quantifier_join M depth true p q a b HAllA HAllB).
 eapply source_cutoff_shift_binary;[right;right;reflexivity|exact HImpA|exact HImpB|
 exact(source_cutoff_shift_fixes_domain M depth domain HD)|exact HI].
Qed.
Theorem source_L_cut_witness_shift M domain theta other a b:
 source_bounded M domain(code_numeral M 1) ->source_cutoff_shift M 2 theta other ->
 code_relation M(schema_env3 domain theta(zeroM M))(E_L_cut_witness(CEvar 0)(CEvar 1))a ->
 code_relation M(schema_env3 domain other(zeroM M))(E_L_cut_witness(CEvar 0)(CEvar 1))b ->source_formula_shift M a b.
Proof.
 intros HD HT HA HB. unfold E_L_cut_witness,E_sf_ex in HA,HB.
 destruct(schema_expression_quantifier_split M _ SFEx _ a HA)as(ab&HAB&HExA).
 destruct(schema_expression_quantifier_split M _ SFEx _ b HB)as(bb&HBB&HExB).
 destruct(schema_expression_split M _ SFAnd _ _ ab HAB)as(d&pa&HDa&HPA&HAndA).
 destruct(schema_expression_split M _ SFAnd _ _ bb HBB)as(d'&pb&HDb&HPB&HAndB).
 change(d=domain)in HDa. change(d'=domain)in HDb. subst d d'.
 apply source_cutoff_zero_is_shift. apply(source_cutoff_quantifier_join M 0 false ab bb a b HExA HExB).
 eapply source_cutoff_shift_binary;[left;reflexivity|exact HAndA|exact HAndB|
 exact(source_cutoff_shift_fixes_domain M 0 domain HD)|].
 exact(source_L_range_profile_cutoff M 1 domain theta other 1 pa pb HD HT HPA HPB).
Qed.
Print Assumptions source_L_range_profile_cutoff.
Print Assumptions source_L_cut_witness_shift.



