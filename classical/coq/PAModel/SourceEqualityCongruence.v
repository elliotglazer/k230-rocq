(** Genuine PA-definable induction proving equality congruence for every
    internal source formula. Substitutions and formulas may be nonstandard. *)
From PAModel Require Import Model NumericalProofs FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetCodeDescent
 SourceBounded NumericalSubstitutionMaps NumericalSubstitution SubstitutionPayloads NumericalRenaming NumericalContextRenaming
 SourceConditionalProofs SourceConditionalBinary SourceConditionalQuantifiers SourceConditionalAtoms
 SourceEqualitySupport SourceEqualityAtomFacts SourceImplicationAllShift SourceQuantifierRules.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_equality_congruence_at M f:=forall condition k rb rc rn base sb sc sn sbase a b q,
 source_bounded M f k ->source_bounded M condition q ->source_bounded M a q ->source_bounded M b q ->
 numerical_substitution M f rb rc rn base a ->numerical_substitution M f sb sc sn sbase b ->
 source_equal_substitutions M condition k rb rc rn base sb sc sn sbase ->
 source_conditional_equivalent M condition a b.
Definition source_equality_congruence_formula:form:=
 ∀∀∀∀∀∀∀∀∀∀∀∀∀(
 source_bounded_accept_formula $13 $11 →source_bounded_accept_formula $12 $0 →
 source_bounded_accept_formula $2 $0 →source_bounded_accept_formula $1 $0 →
 numerical_substitution_formula $13 $10 $9 $8 $7 $2 →numerical_substitution_formula $13 $6 $5 $4 $3 $1 →
 source_equal_substitutions_formula $12 $11 $10 $9 $8 $7 $6 $5 $4 $3 →
 (source_conditional_implies_formula $12 $2 $1 ∧source_conditional_implies_formula $12 $1 $2)).
Local Opaque holds source_bounded_accept_formula numerical_substitution_formula
 source_equal_substitutions_formula source_conditional_implies_formula.
Lemma source_equality_congruence_definable M:Definable1 M(source_equality_congruence_at M).
Proof.
 exists source_equality_congruence_formula,(fun _=>zeroM M). intro f.
 unfold source_equality_congruence_formula,source_equality_congruence_at,source_conditional_equivalent.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp. setoid_rewrite holds_and.
 setoid_rewrite source_bounded_accept_formula_correct. setoid_rewrite numerical_substitution_formula_correct.
 setoid_rewrite source_equal_substitutions_formula_correct. setoid_rewrite source_conditional_implies_formula_correct.
 reflexivity.
Qed.

Lemma source_equality_congruence_atom M equality i j f:
 sf_relation M(source_equality_atom equality)i j f ->source_equality_congruence_at M f.
Proof.
 intros HF condition k rb rc rn base sb sc sn sbase a b q BF BC BA BB HRA HSB Support.
 destruct(proj1(numerical_substitution_atom M equality i j f rb rc rn base a HF)HRA)as(x&y&HX&HY&HA).
 destruct(proj1(numerical_substitution_atom M equality i j f sb sc sn sbase b HF)HSB)as(d&e&HD&HE&HB).
 pose proof(source_equality_atom_is_atom equality)as HH.
 destruct(proj1(source_bounded_accept_atom M _ i j f k HH HF)BF)as[BI BJ].
 destruct(proj1(source_bounded_accept_atom M _ x y a q HH HA)BA)as[BX BY].
 destruct(proj1(source_bounded_accept_atom M _ d e b q HH HB)BB)as[BD BE].
 destruct(sf_relation_total M SFEqual x d)as(equal1&H1).
 destruct(sf_relation_total M SFEqual y e)as(equal2&H2).
 pose proof(Support i x d equal1 BI HX HD H1)as P1.
 pose proof(Support j y e equal2 BJ HY HE H2)as P2.
 split.
 - exact(source_conditional_atom M equality condition x y d e a b equal1 equal2 q BC BX BY BD BE HA HB H1 H2 P1 P2).
 - destruct(sf_relation_total M SFEqual d x)as(reverse1&HR1).
   destruct(sf_relation_total M SFEqual e y)as(reverse2&HR2).
   exact(source_conditional_atom M equality condition d e x y b a reverse1 reverse2 q BC BD BE BX BY HB HA HR1 HR2
    (source_conditional_equal_symmetric M condition x d equal1 reverse1 q BC BX BD H1 HR1 P1)
    (source_conditional_equal_symmetric M condition y e equal2 reverse2 q BC BY BE H2 HR2 P2)).
Qed.

Theorem source_equality_congruence_internal M f:source_equality_congruence_at M f.
Proof.
 revert f. apply(sf_code_induction M(source_equality_congruence_at M)(source_equality_congruence_definable M)).
 - intros condition k rb rc rn base sb sc sn sbase a b q BF BC BA BB HRA HSB Support.
   pose proof(proj1(numerical_substitution_invalid M _ rb rc rn base a(or_introl eq_refl))HRA)as EA.
   pose proof(proj1(numerical_substitution_invalid M _ sb sc sn sbase b(or_introl eq_refl))HSB)as EB.
   subst a b. split;exact(source_conditional_implies_refl M condition(zeroM M)q BC(source_bounded_accept_falsity M q)).
 - intros f Invalid condition k rb rc rn base sb sc sn sbase a b q BF BC BA BB HRA HSB Support.
   pose proof(proj1(numerical_substitution_invalid M f rb rc rn base a(or_intror Invalid))HRA)as EA.
   pose proof(proj1(numerical_substitution_invalid M f sb sc sn sbase b(or_intror Invalid))HSB)as EB.
   subst a b. split;exact(source_conditional_implies_refl M condition(zeroM M)q BC(source_bounded_accept_falsity M q)).
 - exact(fun i j f H=>source_equality_congruence_atom M false i j f H).
 - exact(fun i j f H=>source_equality_congruence_atom M true i j f H).
 - intros h u v f HH HF IHU IHV condition k rb rc rn base sb sc sn sbase a b q BF BC BA BB HRA HSB Support.
   destruct(proj1(numerical_substitution_binary M h u v f rb rc rn base a HH HF)HRA)as(ua&va&HUA&HVA&HA).
   destruct(proj1(numerical_substitution_binary M h u v f sb sc sn sbase b HH HF)HSB)as(ub&vb&HUB&HVB&HB).
   destruct(proj1(source_bounded_accept_binary M h u v f k HH HF)BF)as[BU BV].
   destruct(proj1(source_bounded_accept_binary M h ua va a q HH HA)BA)as[BUA BVA].
   destruct(proj1(source_bounded_accept_binary M h ub vb b q HH HB)BB)as[BUB BVB].
   pose proof(IHU condition k rb rc rn base sb sc sn sbase ua ub q BU BC BUA BUB HUA HUB Support)as PEU.
   pose proof(IHV condition k rb rc rn base sb sc sn sbase va vb q BV BC BVA BVB HVA HVB Support)as PEV.
   split.
   + exact(source_conditional_implies_binary M h condition ua va ub vb a b q HH BC BUA BVA BUB BVB PEU(proj1 PEV)HA HB).
   + exact(source_conditional_implies_binary M h condition ub vb ua va b a q HH BC BUB BVB BUA BVA
     (conj(proj2 PEU)(proj1 PEU))(proj2 PEV)HB HA).
 - intros h u f HH HF IHU condition k rb rc rn base sb sc sn sbase a b q BF BC BA BB HRA HSB Support.
   assert(Quantifier:exists universal,h=substitution_source_quantifier universal).
   { destruct HH as[EH|EH];subst h;[exists true|exists false];reflexivity. }
   destruct Quantifier as(universal&EH). subst h.
   destruct(proj1(numerical_substitution_quantifier M universal u f rb rc rn base a HF)HRA)
    as(rd&re&rm&ua&HLR&HUA&HA).
   destruct(proj1(numerical_substitution_quantifier M universal u f sb sc sn sbase b HF)HSB)
    as(sd&se&sm&ub&HLS&HUB&HB).
   pose proof(proj1(source_bounded_accept_unary M _ u f k HH HF)BF)as BU.
   pose proof(proj1(source_bounded_accept_unary M _ ua a q HH HA)BA)as BUA.
   pose proof(proj1(source_bounded_accept_unary M _ ub b q HH HB)BB)as BUB.
   destruct(numerical_renaming_total M condition(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(shifted&HS).
   pose proof(source_equal_substitutions_lift M condition shifted k rb rc rn base sb sc sn sbase rd re rm sd se sm q
    BC HS Support HLR HLS)as Lifted.
   pose proof(IHU shifted(succM M k)rd re rm(succM M base)sd se sm(succM M sbase)ua ub(succM M q)
    BU(source_shift_bound M condition shifted q BC HS)BUA BUB HUA HUB Lifted)as PE.
   split.
   + exact(source_conditional_implies_quantifier M _ condition shifted ua ub a b q HH BC HS BUA BUB HA HB(proj1 PE)).
   + exact(source_conditional_implies_quantifier M _ condition shifted ub ua b a q HH BC HS BUB BUA HB HA(proj2 PE)).
Qed.
Print Assumptions source_equality_congruence_definable.
Print Assumptions source_equality_congruence_internal.
