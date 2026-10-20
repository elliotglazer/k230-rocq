(** Actual uniform representation existence by a PA-definable induction
    on arbitrary internal source syntax. No constructor/existence family is
    retained as a premise. Both assignment counts and matrices may be nonstandard. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes SetCodeDescent SourceBounded
 SourceRepresentationRecipe SourceRepresentationClosureRecipe SourceRepresentationClosureArithmetic SourceZFRProvability
 SourceZFRFalsityRepresentation SourceRepresentationAtom SourceRepresentationConjunctionExistence SourceRepresentationDisjunctionExistence
 SourceRepresentationImplication SourceRepresentationExistential SourceRepresentationUniversal.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature |0.
#[local] Existing Instance PA_preds_signature |0.
Definition source_representation_exists_at M phi:=forall count out,
 source_bounded M phi count->source_representation_in_closure_recipe M count phi out->source_zfr_provable M out.
Definition source_representation_exists_formula:form:=∀∀(source_bounded_accept_formula $2 $1→
 source_representation_in_closure_recipe_formula $1 $2 $0→source_zfr_provable_formula $0).
Local Opaque holds source_bounded_accept_formula source_representation_in_closure_recipe_formula source_zfr_provable_formula.
Theorem source_representation_exists_definable M:Definable1 M(source_representation_exists_at M).
Proof.
 exists source_representation_exists_formula,(fun _=>zeroM M). intro phi.
 unfold source_representation_exists_formula,source_representation_exists_at.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
 setoid_rewrite source_bounded_accept_formula_correct.
 setoid_rewrite source_representation_in_closure_recipe_formula_correct.
 setoid_rewrite source_zfr_provable_formula_correct. reflexivity.
Qed.
Theorem source_zfr_representation_uniform M:forall phi,source_representation_exists_at M phi.
Proof.
 apply(sf_code_induction M(source_representation_exists_at M)).
 - apply source_representation_exists_definable.
 - intros count out BF HR. exact(source_zfr_falsity_representation M count out HR).
 - intros phi HInvalid count out BF HR. exfalso. exact(source_bounded_reject_invalid M phi count HInvalid BF).
 - intros i j phi HAtom count out BF HR. exact(source_zfr_representation_atom M true count i j phi out BF HAtom HR).
 - intros i j phi HAtom count out BF HR. exact(source_zfr_representation_atom M false count i j phi out BF HAtom HR).
 - intros h a b phi HH HBinary IHa IHb count out BF HR.
   destruct(proj1(source_bounded_accept_binary M h a b phi count HH HBinary)BF)as[BA BB].
   destruct HH as[HA|[HO|HI]];subst h.
   + exact(source_zfr_representation_conjunction M count a b phi out BF HBinary(fun r HP=>IHa count r BA HP)(fun r HP=>IHb count r BB HP)HR).
   + exact(source_zfr_representation_disjunction M count a b phi out BF HBinary(fun r HP=>IHa count r BA HP)(fun r HP=>IHb count r BB HP)HR).
   + exact(source_zfr_representation_implication M count a b phi out BF HBinary(fun r HP=>IHa count r BA HP)(fun r HP=>IHb count r BB HP)HR).
 - intros h a phi HH HQuant IH count out BF HR.
   pose proof(proj1(source_bounded_accept_unary M h a phi count HH HQuant)BF)as BA.
   destruct HH as[HA|HE];subst h.
   + exact(source_zfr_representation_universal M count a phi out BF HQuant(fun r HP=>IH(succM M count)r BA HP)HR).
   + exact(source_zfr_representation_existential M count a phi out BF HQuant(fun r HP=>IH(succM M count)r BA HP)HR).
Qed.
Theorem source_zfr_representation_total M count phi:
 source_bounded M phi count->exists out,source_representation_in_closure_recipe M count phi out/\source_zfr_provable M out.
Proof.
 intro BF. destruct(source_representation_in_closure_recipe_total M count phi)as(out&HR).
 exists out. exact(conj HR(source_zfr_representation_uniform M phi count out BF HR)).
Qed.
Print Assumptions source_representation_exists_definable.
Print Assumptions source_zfr_representation_uniform.
Print Assumptions source_zfr_representation_total.
