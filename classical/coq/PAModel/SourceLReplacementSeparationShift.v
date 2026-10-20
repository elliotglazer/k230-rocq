(** Inserting an unused raw-range slot in the ordinary relative
    Separation axiom shifts its arbitrary matrix above three binders. *)
From PAModel Require Import Model FiniteCoding CodeExpressions ProofTemplates SetFormulaCodes SetSchemaConstructors SourceBounded
 SourceQuantifierRules SourceFiniteCutoffShift SourceCutoffShiftConstructors SourceCutoffQuantifiers SourceCutoffPropositional
 SourcePropositionalRebase SourceWFSeparationConstructor SourceFunctionalityShells
 SourceLReplacementCutShells SourceLReplacementBoundCut.
Unset Implicit Arguments.
Theorem source_L_separation_law_shift M domain first second a b:
 source_bounded M domain(code_numeral M 1) ->source_cutoff_shift M 3 first second ->
 code_relation M(schema_env3 domain first(zeroM M))(E_L_separation_law(CEvar 0)(CEvar 1))a ->
 code_relation M(schema_env3 domain second(zeroM M))(E_L_separation_law(CEvar 0)(CEvar 1))b ->source_formula_shift M a b.
Proof.
 intros HD HM HA HB.
 unfold E_L_separation_law,E_sf_all in HA,HB.
 destruct(schema_expression_quantifier_split M _ SFAll _ a HA)as(ag&HAG&HAllA).
 destruct(schema_expression_quantifier_split M _ SFAll _ b HB)as(bg&HBG&HAllB).
 destruct(schema_expression_split M _ SFImpl _ _ ag HAG)as(d&ae&HDA&HAE&HImpA).
 destruct(schema_expression_split M _ SFImpl _ _ bg HBG)as(d'&be&HDB&HBE&HImpB).
 change(d=domain)in HDA. change(d'=domain)in HDB. subst d d'.
 unfold E_L_selection_witness,E_sf_ex in HAE,HBE.
 destruct(schema_expression_quantifier_split M _ SFEx _ ae HAE)as(ab&HAB&HExA).
 destruct(schema_expression_quantifier_split M _ SFEx _ be HBE)as(bb&HBB&HExB).
 destruct(schema_expression_split M _ SFAnd _ _ ab HAB)as(d&ap&HDA&HAP&HAndA).
 destruct(schema_expression_split M _ SFAnd _ _ bb HBB)as(d'&bp&HDB&HBP&HAndB).
 change(d=domain)in HDA. change(d'=domain)in HDB. subst d d'.
 destruct(code_relation_total M(E_sf_mem 0 2)(schema_env3 domain first(zeroM M)))as(member&HMember).
 destruct(sf_relation_total M SFAnd member first)as(pa&HPA).
 destruct(sf_relation_total M SFAnd member second)as(pb&HPB).
 assert(HPA':code_relation M(schema_env3 domain first(zeroM M))(E_sf SFAnd(E_sf_mem 0 2)(CEvar 1))pa).
 { exact(source_sf_expression_join M(schema_env3 domain first(zeroM M))SFAnd(E_sf_mem 0 2)(CEvar 1)member first pa HMember eq_refl HPA). }
 assert(HPB':code_relation M(schema_env3 domain second(zeroM M))(E_sf SFAnd(E_sf_mem 0 2)(CEvar 1))pb).
 { exact(source_sf_expression_join M(schema_env3 domain second(zeroM M))SFAnd(E_sf_mem 0 2)(CEvar 1)member second pb HMember eq_refl HPB). }
 assert(HAP':code_relation M(schema_env3 domain pa(zeroM M))(E_L_range_profile(CEvar 0)(CEvar 1)1)ap).
 { apply(proj1(code_subst_graph M(schema_env3 domain first(zeroM M))
    (fun i=>match i with 0=>CEvar 0|1=>E_sf SFAnd(E_sf_mem 0 2)(CEvar 1)|_=>CEconst 0 end)
    (schema_env3 domain pa(zeroM M))ltac:(intros[|[|i]];cbn[schema_env3];try reflexivity;exact HPA')
     (E_L_range_profile(CEvar 0)(CEvar 1)1)ap)). exact HAP. }
 assert(HBP':code_relation M(schema_env3 domain pb(zeroM M))(E_L_range_profile(CEvar 0)(CEvar 1)1)bp).
 { apply(proj1(code_subst_graph M(schema_env3 domain second(zeroM M))
    (fun i=>match i with 0=>CEvar 0|1=>E_sf SFAnd(E_sf_mem 0 2)(CEvar 1)|_=>CEconst 0 end)
    (schema_env3 domain pb(zeroM M))ltac:(intros[|[|i]];cbn[schema_env3];try reflexivity;exact HPB')
     (E_L_range_profile(CEvar 0)(CEvar 1)1)bp)). exact HBP. }
 assert(HMatrix:source_cutoff_shift M 3 pa pb).
 { eapply source_cutoff_shift_binary;[left;reflexivity|exact HPA|exact HPB| |exact HM].
   exact(source_cutoff_shift_fixed_member M 3 0 2 member member HMember HMember). }
 pose proof(source_L_range_profile_cutoff M 2 domain pa pb 1 ap bp HD HMatrix HAP' HBP')as HProfile.
 assert(HBody:source_cutoff_shift M 2 ab bb).
 { eapply source_cutoff_shift_binary;[left;reflexivity|exact HAndA|exact HAndB|
    exact(source_cutoff_shift_fixes_domain M 1 domain HD)|exact HProfile]. }
 pose proof(source_cutoff_quantifier_join M 1 false ab bb ae be HExA HExB HBody)as HExists.
 assert(HGuard:source_cutoff_shift M 1 ag bg).
 { eapply source_cutoff_shift_binary;[right;right;reflexivity|exact HImpA|exact HImpB|
    exact(source_cutoff_shift_fixes_domain M 0 domain HD)|exact HExists]. }
 exact(source_cutoff_zero_is_shift M a b(source_cutoff_quantifier_join M 0 true ag bg a b HAllA HAllB HGuard)).
Qed.
Print Assumptions source_L_separation_law_shift.




