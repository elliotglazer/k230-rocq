(** A genuine arithmetic syntax transformation on arbitrary internal
    source codes.  This graph contains no source-provability predicate. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  SetFormulaCodes SetCodeDescent CodeTuples NumericalTraces SentenceBounds
  SourceRelativizationRules.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_relativization M d f v := exists r,
  sr_record M d f v r /\ trace_derives M source_relativization_rules r.
Definition source_relativization_formula (d f v:term) : form :=
  ∃ (sr_record_formula d`[↑] f`[↑] v`[↑] $0 ∧
    trace_derives_formula source_relativization_rules $0).

Local Opaque holds sr_record_formula trace_derives_formula.
Theorem source_relativization_formula_correct M rho d f v :
  holds M rho (source_relativization_formula d f v) <->
  source_relativization M (evalM M rho d) (evalM M rho f) (evalM M rho v).
Proof.
  unfold source_relativization_formula,source_relativization.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite sr_record_formula_correct. setoid_rewrite trace_derives_formula_correct.
  unfold evalM. now setoid_rewrite eval_up.
Qed.

Lemma source_relativization_leaf M d f v :
  sr_leaf M f v -> source_relativization M d f v.
Proof.
  intro H. destruct (sr_record_total M d f v) as [r HR]. exists r.
  split;[exact HR|]. apply trace_derives_base,sr_rule_base. exists d,f,v. auto.
Qed.

Theorem source_relativization_falsity M d : source_relativization M d (zeroM M) (zeroM M).
Proof. apply source_relativization_leaf. left. auto. Qed.

Theorem source_relativization_invalid M d f :
  sf_invalid M f -> source_relativization M d f (zeroM M).
Proof. intro H. apply source_relativization_leaf. left. auto. Qed.

Theorem source_relativization_atom M d h a b f :
  (h=SFMember \/ h=SFEqual) -> sf_relation M h a b f ->
  source_relativization M d f f.
Proof.
  intros [Hh|Hh] H;subst h;apply source_relativization_leaf;right;exists a,b;auto.
Qed.

Theorem source_relativization_binary M d h a b f x y v :
  sf_binary h -> sf_relation M h a b f ->
  source_relativization M d a x -> source_relativization M d b y ->
  sf_relation M h x y v -> source_relativization M d f v.
Proof.
  intros Hh Hf [p [HP HDP]] [q [HQ HDQ]] HV.
  destruct (sr_record_total M d f v) as [r HR]. exists r. split;[exact HR|].
  apply (trace_derives_binary M source_relativization_rules r p q HDP HDQ),sr_rule_binary.
  exists d,f,v,a,b,x,y. repeat split;try assumption.
  destruct Hh as [Hh|[Hh|Hh]];subst h;unfold sr_binary_heads;auto.
Qed.

Definition sr_source_quantifier (universal:bool) := if universal then SFAll else SFEx.
Theorem source_relativization_quantifier M d universal a f w v :
  sf_relation M (sr_source_quantifier universal) a (zeroM M) f ->
  source_relativization M d a w -> sr_quantifier M universal d w v ->
  source_relativization M d f v.
Proof.
  intros Hf [p [HP HDP]] HV.
  destruct (sr_record_total M d f v) as [r HR]. exists r. split;[exact HR|].
  apply (trace_derives_unary M source_relativization_rules r p HDP),sr_rule_unary.
  exists d,f,v,a,w. repeat split;try assumption.
  destruct universal;unfold sr_source_quantifier in Hf;auto.
Qed.

Definition source_relativization_total_formula : form :=
  ∀∃ source_relativization_formula $1 $2 $0.
Lemma source_relativization_total_definable M : Definable1 M
  (fun f=>forall d,exists v,source_relativization M d f v).
Proof.
  exists source_relativization_total_formula,(fun _=>zeroM M).
  intro f. unfold source_relativization_total_formula.
  setoid_rewrite holds_all. setoid_rewrite holds_ex.
  setoid_rewrite source_relativization_formula_correct. reflexivity.
Qed.

Theorem source_relativization_total M d f : exists v,source_relativization M d f v.
Proof.
  revert f d. apply (sf_code_induction M (fun f=>forall d,exists v,source_relativization M d f v)).
  - apply source_relativization_total_definable.
  - intro d. exists (zeroM M). apply source_relativization_falsity.
  - intros f HF d. exists (zeroM M). now apply source_relativization_invalid.
  - intros a b f HF d. exists f. exact (source_relativization_atom M d SFMember a b f (or_introl eq_refl) HF).
  - intros a b f HF d. exists f. exact (source_relativization_atom M d SFEqual a b f (or_intror eq_refl) HF).
  - intros h a b f HH HF IHa IHb d. destruct (IHa d) as [x HX]. destruct (IHb d) as [y HY].
    destruct (sf_relation_total M h x y) as [v HV]. exists v.
    exact (source_relativization_binary M d h a b f x y v HH HF HX HY HV).
  - intros h a f HH HF IH d. destruct (IH d) as [w HW].
    destruct HH as [HH|HH];subst h.
    + destruct (sr_quantifier_total M true d w) as [v HV]. exists v.
      exact (source_relativization_quantifier M d true a f w v HF HW HV).
    + destruct (sr_quantifier_total M false d w) as [v HV]. exists v.
      exact (source_relativization_quantifier M d false a f w v HF HW HV).
Qed.

Theorem source_relativization_formula_bound :
  bounded 3 (source_relativization_formula $0 $1 $2).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Print Assumptions source_relativization_formula_correct.
Print Assumptions source_relativization_falsity.
Print Assumptions source_relativization_atom.
Print Assumptions source_relativization_binary.
Print Assumptions source_relativization_quantifier.
Print Assumptions source_relativization_total.
