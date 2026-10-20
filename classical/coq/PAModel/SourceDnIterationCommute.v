(** The same Dn step may be moved from the end of an internally long
 iteration to its beginning. This is PA-definable syntax induction. *)
From PAModel Require Import Model CodeExpressions NumericalProofs SourceDn SourceDnStep.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature |0.
#[local] Existing Instance PA_preds_signature |0.
Definition source_dn_commute_at M count:=forall body first previous result,
 source_dn_successor M body first ->source_dn M count body previous ->
 source_dn_successor M previous result ->source_dn M count first result.
Definition source_dn_commute_formula:form:=∀∀∀∀(
 source_dn_successor_formula $3 $2 →source_dn_formula $4 $3 $1 →
 source_dn_successor_formula $1 $0 →source_dn_formula $4 $2 $0).
Local Opaque holds source_dn_successor_formula source_dn_formula.
Lemma source_dn_commute_definable M:Definable1 M(source_dn_commute_at M).
Proof.
 exists source_dn_commute_formula,(fun _=>zeroM M). intro count.
 unfold source_dn_commute_formula,source_dn_commute_at.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
 setoid_rewrite source_dn_successor_formula_correct. setoid_rewrite source_dn_formula_correct. reflexivity.
Qed.
Theorem source_dn_successor_commute M:forall count,source_dn_commute_at M count.
Proof.
 apply(definable_induction M(source_dn_commute_at M)(source_dn_commute_definable M)).
 - intros body first previous result HF HD HR. apply source_dn_zero in HD. subst previous.
   apply source_dn_zero. symmetry. exact(source_dn_successor_functional M body first result HF HR).
 - intros count IH body first previous result HF HD HR.
   apply source_dn_succ in HD. destruct HD as(p&HP&HPrevious).
   apply source_dn_succ. exists previous. split;[|exact HR].
   exact(IH body first p previous HF HP HPrevious).
Qed.
Theorem source_dn_succ_first M count body result:
 source_dn M(succM M count)body result <->exists first,
 source_dn_successor M body first /\source_dn M count first result.
Proof.
 split.
 - intro HD. apply source_dn_succ in HD. destruct HD as(previous&HPrevious&HResult).
   destruct(source_dn_successor_total M body)as(first&HFirst).
   exists first. exact(conj HFirst(source_dn_successor_commute M count body first previous result HFirst HPrevious HResult)).
 - intros(first&HFirst&HD).
   destruct(source_dn_total M(succM M count)body)as(other&HOther).
   apply source_dn_succ in HOther. destruct HOther as(previous&HPrevious&HStep).
   pose proof(source_dn_successor_commute M count body first previous other HFirst HPrevious HStep)as HT.
   assert(E:result=other)by(eapply source_dn_functional;eassumption). subst result.
   apply source_dn_succ. exists previous. exact(conj HPrevious HStep).
Qed.
Print Assumptions source_dn_commute_definable.
Print Assumptions source_dn_successor_commute.
Print Assumptions source_dn_succ_first.
