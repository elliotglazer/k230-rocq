(** The literal attempt-existence subset and its actual arbitrary-name AllE rule. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourcePropositionalTemplates SourcePropositionalRebase SourcePropositionalSubstitution SourceFunctionalityShells
 SourceRecursionPrimitiveRelations SourceRecursionExistsAttempt SourceRecursionExACutoff NumericalSubstitutionMaps NumericalSubstitution
 NumericalInstantiation SubstitutionSource SourceInstantiationConstructors NumericalContexts NumericalSourceFull SourceTraceBounds.
Unset Implicit Arguments.
Definition source_rec_exa_subset_template:=SPTAnd
 (SPTImpl(SPTSlot 0)(SPTAnd(SPTSlot 1)(SPTSlot 2)))
 (SPTImpl(SPTAnd(SPTSlot 1)(SPTSlot 2))(SPTSlot 0)).
Definition source_rec_exa_subset_point M phi o a N X z out:=exists memberX memberN agr,
 sf_relation M SFMember z X memberX /\sf_relation M SFMember z N memberN /\source_rec_exa M phi z o a N agr /\
 code_relation M(source_rec_env3 memberX memberN agr)(source_prop_expression source_rec_exa_subset_template)out.
Definition source_rec_exa_subset_chart M phi o a N X out:=exists point,
 source_rec_exa_subset_point M phi(succM M o)(succM M a)(succM M N)(succM M X)(zeroM M)point /\sf_relation M SFAll point(zeroM M)out.
Theorem source_rec_exa_subset_point_total M phi o a N X z:exists out,source_rec_exa_subset_point M phi o a N X z out.
Proof.
 destruct(sf_relation_total M SFMember z X)as(mx&HX). destruct(sf_relation_total M SFMember z N)as(mn&HN).
 destruct(source_rec_exa_total M phi z o a N)as(agr&HA).
 destruct(code_relation_total M(source_prop_expression source_rec_exa_subset_template)(source_rec_env3 mx mn agr))as(out&HO).
 exists out,mx,mn,agr. auto.
Qed.
Theorem source_rec_exa_subset_chart_total M phi o a N X:exists out,source_rec_exa_subset_chart M phi o a N X out.
Proof.
 destruct(source_rec_exa_subset_point_total M phi(succM M o)(succM M a)(succM M N)(succM M X)(zeroM M))as(point&HP).
 destruct(sf_relation_total M SFAll point(zeroM M))as(out&HO). exists out,point. auto.
Qed.
Theorem source_rec_exa_subset_point_functional M phi o a N X z out out':
 source_rec_exa_subset_point M phi o a N X z out ->source_rec_exa_subset_point M phi o a N X z out' ->out=out'.
Proof.
 intros(mx&mn&agr&HX&HN&HA&HO)(mx'&mn'&agr'&HX'&HN'&HA'&HO').
 pose proof(sf_relation_functional M SFMember z X mx' mx HX' HX)as E. subst mx'.
 pose proof(sf_relation_functional M SFMember z N mn' mn HN' HN)as E. subst mn'.
 pose proof(source_rec_exa_functional M phi z o a N agr' agr HA' HA)as E. subst agr'.
 exact(code_relation_functional M _ _ out out' HO HO').
Qed.
Theorem source_rec_exa_subset_point_bounded M phi o a N X z out k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M X k ->coding_lt M z k ->
 source_rec_exa_subset_point M phi o a N X z out ->source_bounded M out k.
Proof.
 intros BP BO BA BN BX BZ(mx&mn&agr&HX&HN&HA&HO).
 apply(source_prop_template_bound M(source_rec_env3 mx mn agr)source_rec_exa_subset_template k);[|exact HO].
 intros[|[|i]];cbn[source_rec_env3].
 - exact(proj2(source_bounded_accept_atom M SFMember z X mx k(or_introl eq_refl)HX)(conj BZ BX)).
 - exact(proj2(source_bounded_accept_atom M SFMember z N mn k(or_introl eq_refl)HN)(conj BZ BN)).
 - exact(source_rec_exa_bounded M phi z o a N agr k BP BZ BO BA BN HA).
Qed.
Theorem source_rec_exa_subset_point_substitution M phi o a N X z out o' a' N' X' z' out' rb rc rn base:
 source_bounded M phi(code_numeral M 2) ->source_rec_exa_subset_point M phi o a N X z out ->source_rec_exa_subset_point M phi o' a' N' X' z' out' ->
 substitution_lookup M rb rc rn base o o' ->substitution_lookup M rb rc rn base a a' ->substitution_lookup M rb rc rn base N N' ->
 substitution_lookup M rb rc rn base X X' ->substitution_lookup M rb rc rn base z z' ->numerical_substitution M out rb rc rn base out'.
Proof.
 intros BP(mx&mn&agr&HX&HN&HA&HO)(mx'&mn'&agr'&HX'&HN'&HA'&HO')HOO HAA HNMap HXMap HZ.
 apply(source_prop_expression_substitution M(source_rec_env3 mx mn agr)(source_rec_env3 mx' mn' agr')rb rc rn base source_rec_exa_subset_template);[|exact HO|exact HO'].
 intros[|[|i]];cbn[source_rec_env3].
 - apply(proj2(numerical_substitution_member M z X mx rb rc rn base mx' HX)). exists z',X'. auto.
 - apply(proj2(numerical_substitution_member M z N mn rb rc rn base mn' HN)). exists z',N'. auto.
 - exact(source_rec_exa_substitution M phi z o a N agr z' o' a' N' agr' rb rc rn base BP HA HA' HZ HOO HAA HNMap).
Qed.
Theorem source_rec_exa_subset_chart_substitution M phi o a N X out o' a' N' X' out' rb rc rn base:
 source_bounded M phi(code_numeral M 2) ->source_rec_exa_subset_chart M phi o a N X out ->source_rec_exa_subset_chart M phi o' a' N' X' out' ->
 substitution_lookup M rb rc rn base o o' ->substitution_lookup M rb rc rn base a a' ->substitution_lookup M rb rc rn base N N' ->
 substitution_lookup M rb rc rn base X X' ->numerical_substitution M out rb rc rn base out'.
Proof.
 intros BP(point&HP&HO)(point'&HP'&HO')HOO HAA HN HX.
 destruct(substitution_lift_total M rb rc rn base)as(lb&lc&ln&HL).
 apply(proj2(numerical_substitution_quantifier M true point out rb rc rn base out' HO)).
 exists lb,lc,ln,point'. split;[exact HL|]. split;[|exact HO'].
 exact(source_rec_exa_subset_point_substitution M phi _ _ _ _ _ point _ _ _ _ _ point' lb lc ln(succM M base)BP HP HP'
  (proj2(proj2 HL)o o' HOO)(proj2(proj2 HL)a a' HAA)(proj2(proj2 HL)N N' HN)(proj2(proj2 HL)X X' HX)(proj1(proj2 HL))).
Qed.
Theorem source_full_rec_exa_subset_chart_use M cb cc cn phi o a N X chart z result:
 source_bounded M phi(code_numeral M 2) ->source_rec_exa_subset_chart M phi o a N X chart ->source_rec_exa_subset_point M phi o a N X z result ->
 source_full_prv M cb cc cn chart ->source_full_prv M cb cc cn result.
Proof.
 intros BP(point&HP&HO)HR PC.
 destruct(substitution_singleton_total M z)as(rb&rc&HHead&_).
 assert(HInst:numerical_instantiation M point z result).
 { exists rb,rc. split;[exact HHead|].
   exact(source_rec_exa_subset_point_substitution M phi _ _ _ _ _ point o a N X z result rb rc(code_numeral M 1)(zeroM M)BP HP HR
    (substitution_singleton_tail M rb rc o)(substitution_singleton_tail M rb rc a)
    (substitution_singleton_tail M rb rc N)(substitution_singleton_tail M rb rc X)HHead). }
 exact(full_source_AllE M cb cc cn point chart z result
  (source_wf_quantifier_instance M cb cc cn SFAll point chart z result(or_introl eq_refl)HO(source_full_prv_wellformed M cb cc cn chart PC)HInst)
  PC HO HInst).
Qed.
Theorem source_rec_exa_subset_point_shell M phi o a N X z out:
 source_rec_exa_subset_point M phi o a N X z out ->exists memberX memberN agr both forward backward,
 sf_relation M SFMember z X memberX /\sf_relation M SFMember z N memberN /\source_rec_exa M phi z o a N agr /\
 sf_relation M SFAnd memberN agr both /\sf_relation M SFImpl memberX both forward /\sf_relation M SFImpl both memberX backward /\
 sf_relation M SFAnd forward backward out.
Proof.
 intros(mx&mn&agr&HX&HN&HA&HO).
 destruct(sf_relation_total M SFAnd mn agr)as(both&HB).
 destruct(sf_relation_total M SFImpl mx both)as(forward&HF).
 destruct(sf_relation_total M SFImpl both mx)as(backward&HR).
 destruct(sf_relation_total M SFAnd forward backward)as(target&HT).
 assert(HG:code_relation M(source_rec_env3 mx mn agr)(source_prop_expression source_rec_exa_subset_template)target).
 { unfold source_rec_exa_subset_template. cbn[source_prop_expression]. functionality_graph. }
 rewrite(code_relation_functional M _ _ out target HO HG).
 exists mx,mn,agr,both,forward,backward. auto 12.
Qed.
Print Assumptions source_rec_exa_subset_point_total.
Print Assumptions source_rec_exa_subset_chart_total.
Print Assumptions source_rec_exa_subset_point_functional.
Print Assumptions source_rec_exa_subset_point_bounded.
Print Assumptions source_rec_exa_subset_point_substitution.
Print Assumptions source_rec_exa_subset_chart_substitution.
Print Assumptions source_full_rec_exa_subset_chart_use.
Print Assumptions source_rec_exa_subset_point_shell.
