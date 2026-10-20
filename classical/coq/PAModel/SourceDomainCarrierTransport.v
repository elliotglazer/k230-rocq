(** Literal containment of a carrier in a unary numerical-source domain. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceRelativizationBounds
 NumericalSubstitutionMaps NumericalSubstitution SourceSubstitutionIdentity SourceDomainInstances
 NumericalRenaming RenamingSubstitution SourceQuantifierRules SourceRecursionShiftGraphs.
Unset Implicit Arguments.
Definition source_domain_carrier M domain carrier out:=exists guard point,
 sf_relation M SFMember(zeroM M)(succM M carrier)guard /\sf_relation M SFImpl guard domain point /\sf_relation M SFAll point(zeroM M)out.
Theorem source_domain_carrier_total M domain carrier:exists out,source_domain_carrier M domain carrier out.
Proof.
 destruct(sf_relation_total M SFMember(zeroM M)(succM M carrier))as(g&HG).
 destruct(sf_relation_total M SFImpl g domain)as(p&HP).
 destruct(sf_relation_total M SFAll p(zeroM M))as(out&HO). exists out,g,p. auto.
Qed.
Theorem source_domain_carrier_substitution M domain carrier old carrier' new rb rc rn base:
 source_bounded M domain(code_numeral M 1) ->source_domain_carrier M domain carrier old ->source_domain_carrier M domain carrier' new ->
 substitution_lookup M rb rc rn base carrier carrier' ->numerical_substitution M old rb rc rn base new.
Proof.
 intros HD(guard&point&HG&HP&HAll)(guard'&point'&HG'&HP'&HAll')HC.
 destruct(substitution_lift_total M rb rc rn base)as(lb&lc&ln&HMap).
 assert(SG:numerical_substitution M guard lb lc ln(succM M base)guard').
 { apply(proj2(numerical_substitution_member M(zeroM M)(succM M carrier)guard lb lc ln(succM M base)guard' HG)).
   exists(zeroM M),(succM M carrier'). split;[exact(proj1(proj2 HMap))|]. split;[exact(proj2(proj2 HMap)carrier carrier' HC)|exact HG']. }
 assert(SD:numerical_substitution M domain lb lc ln(succM M base)domain).
 { apply(numerical_substitution_identity_on_bound M domain lb lc ln(succM M base)(code_numeral M 1)HD).
   intros i HI. rewrite(domain_index_below_one M i HI). exact(proj1(proj2 HMap)). }
 assert(SP:numerical_substitution M point lb lc ln(succM M base)point').
 { apply(proj2(numerical_substitution_binary M SFImpl guard domain point lb lc ln(succM M base)point'(or_intror(or_intror eq_refl))HP)). exists guard',domain. auto. }
 apply(proj2(numerical_substitution_quantifier M true point old rb rc rn base new HAll)). exists lb,lc,ln,point'. auto.
Qed.
Theorem source_domain_carrier_shift M domain carrier old new:
 source_bounded M domain(code_numeral M 1) ->source_domain_carrier M domain carrier old ->
 source_domain_carrier M domain(succM M carrier)new ->source_formula_shift M old new.
Proof.
 intros HD HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero. exact(source_domain_carrier_substitution M domain carrier old(succM M carrier)new(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HD HO HN(source_rec_shift_lookup M carrier)).
Qed.
Print Assumptions source_domain_carrier_total.
Print Assumptions source_domain_carrier_substitution.
Print Assumptions source_domain_carrier_shift.
