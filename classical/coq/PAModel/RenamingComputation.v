(** Internally certified renaming, with an inert padding record field.
    All recursion and trace lengths are arithmetic-model values. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  NumericalProofs SentenceBounds SetFormulaCodes SetCodeDescent
  NumericalEnvironments NumericalRenamingMaps CodeTuples RenamingPayloads NumericalTraces RenamingRules.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition renaming_computation M f b c n k t v := exists r,
  tuple7_graph M f b c n k t v r /\ trace_derives M renaming_rules r.
Definition renaming_computation_formula (f b c n k t v : term) : form :=
  ∃ (tuple7_formula f`[↑] b`[↑] c`[↑] n`[↑] k`[↑] t`[↑] v`[↑] $0 ∧
    trace_derives_formula renaming_rules $0).

Local Opaque holds tuple7_formula trace_derives_formula.
Lemma renaming_computation_formula_correct M rho f b c n k t v :
  holds M rho (renaming_computation_formula f b c n k t v) <->
  renaming_computation M (evalM M rho f) (evalM M rho b) (evalM M rho c)
    (evalM M rho n) (evalM M rho k) (evalM M rho t) (evalM M rho v).
Proof.
  unfold renaming_computation_formula,renaming_computation.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite tuple7_formula_correct. setoid_rewrite trace_derives_formula_correct.
  unfold evalM. now setoid_rewrite eval_up.
Qed.

Lemma renaming_computation_leaf M f b c n k t v :
  renaming_leaf M f b c n k t v -> renaming_computation M f b c n k t v.
Proof.
  intro H. destruct (tuple7_total M f b c n k t v) as [r Hr].
  exists r. split; [exact Hr|]. apply trace_derives_base.
  apply renaming_rule_base. exists f,b,c,n,k,t,v. auto.
Qed.

Lemma renaming_computation_binary M h a d f b c n k t x y v :
  sf_binary h -> sf_relation M h a d f ->
  renaming_computation M a b c n k t x -> renaming_computation M d b c n k t y ->
  renaming_binary M h x y v -> renaming_computation M f b c n k t v.
Proof.
  intros Hh Hf [p [Hp Hdp]] [q [Hq Hdq]] Hv.
  destruct (tuple7_total M f b c n k t v) as [r Hr].
  exists r. split; [exact Hr|]. apply (trace_derives_binary M renaming_rules r p q Hdp Hdq).
  apply renaming_rule_binary. exists f,b,c,n,k,t,v. split; [exact Hr|].
  assert (Hcase : renaming_binary_case M h f b c n k t v p q).
  { exists a,d,x,y. auto. }
  destruct Hh as [Hh|[Hh|Hh]]; subst h; tauto.
Qed.

Lemma renaming_computation_unary M universal a f b c n k t d e m w v :
  sf_relation M (renaming_source_quantifier universal) a (zeroM M) f ->
  renaming_lift M b c n k d e m ->
  renaming_computation M a d e m k t w ->
  renaming_quantifier M universal k t w v -> renaming_computation M f b c n k t v.
Proof.
  intros Hf He [p [Hp Hdp]] Hv.
  destruct (tuple7_total M f b c n k t v) as [r Hr].
  exists r. split; [exact Hr|]. apply (trace_derives_unary M renaming_rules r p Hdp).
  apply renaming_rule_unary. exists f,b,c,n,k,t,v. split; [exact Hr|].
  assert (Hcase : renaming_unary_case M universal f b c n k t v p).
  { exists a,d,e,m,w. auto. }
  destruct universal; tauto.
Qed.

Definition renaming_computation_total_formula : form :=
  ∀∀∀∀∀∃ renaming_computation_formula $6 $5 $4 $3 $2 $1 $0.

Lemma renaming_computation_total_definable M : Definable1 M
  (fun f => forall b c n k t, exists v, renaming_computation M f b c n k t v).
Proof.
  exists renaming_computation_total_formula,(fun _ => zeroM M).
  intro f. unfold renaming_computation_total_formula.
  repeat setoid_rewrite holds_all. setoid_rewrite holds_ex.
  setoid_rewrite renaming_computation_formula_correct. reflexivity.
Qed.

Theorem renaming_computation_total M f b c n k t :
  exists v, renaming_computation M f b c n k t v.
Proof.
  revert f b c n k t. apply (sf_code_induction M
    (fun f => forall b c n k t, exists v, renaming_computation M f b c n k t v)).
  - apply renaming_computation_total_definable.
  - intros b c n k t. exists (zeroM M). apply renaming_computation_leaf.
    left. auto.
  - intros f Hbad b c n k t. exists (zeroM M). apply renaming_computation_leaf.
    left. auto.
  - intros a d f Hf b c n k t.
    destruct (renaming_lookup_total M b c n k a) as [x Hx].
    destruct (renaming_lookup_total M b c n k d) as [y Hy].
    destruct (renaming_atom_total M false x y t k) as [v Hv].
    exists v. apply renaming_computation_leaf. right; left. exists a,d,x,y. auto.
  - intros a d f Hf b c n k t.
    destruct (renaming_lookup_total M b c n k a) as [x Hx].
    destruct (renaming_lookup_total M b c n k d) as [y Hy].
    destruct (renaming_atom_total M true x y t k) as [v Hv].
    exists v. apply renaming_computation_leaf. right; right. exists a,d,x,y. auto.
  - intros h a d f Hh Hf IHa IHd b c n k t.
    destruct (IHa b c n k t) as [x Hx]. destruct (IHd b c n k t) as [y Hy].
    destruct (renaming_binary_total M h x y) as [v Hv].
    exists v. exact (renaming_computation_binary M h a d f b c n k t x y v Hh Hf Hx Hy Hv).
  - intros h a f Hh Hf IHa b c n k t.
    destruct (renaming_lift_total M b c n k) as [d [e [m He]]].
    destruct (IHa d e m k t) as [w Hw].
    destruct Hh as [Hh|Hh]; subst h.
    + destruct (renaming_quantifier_total M true k t w) as [v Hv].
      exists v. exact (renaming_computation_unary M true a f b c n k t d e m w v Hf He Hw Hv).
    + destruct (renaming_quantifier_total M false k t w) as [v Hv].
      exists v. exact (renaming_computation_unary M false a f b c n k t d e m w v Hf He Hw Hv).
Qed.

Lemma renaming_computation_formula_bound :
  bounded 7 (renaming_computation_formula $0 $1 $2 $3 $4 $5 $6).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Print Assumptions renaming_computation_formula_correct.
Print Assumptions renaming_computation_leaf.
Print Assumptions renaming_computation_binary.
Print Assumptions renaming_computation_unary.
Print Assumptions renaming_computation_total.
Print Assumptions renaming_computation_formula_bound.
