(** Internally certified substitution, with an inert padding record field.
    All recursion and trace lengths are arithmetic-model values. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  NumericalProofs SentenceBounds SetFormulaCodes SetCodeDescent
  NumericalEnvironments NumericalSubstitutionMaps CodeTuples SubstitutionPayloads NumericalTraces SubstitutionRules.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition substitution_computation M f b c n k t v := exists r,
  tuple7_graph M f b c n k t v r /\ trace_derives M substitution_rules r.
Definition substitution_computation_formula (f b c n k t v : term) : form :=
  ∃ (tuple7_formula f`[↑] b`[↑] c`[↑] n`[↑] k`[↑] t`[↑] v`[↑] $0 ∧
    trace_derives_formula substitution_rules $0).

Local Opaque holds tuple7_formula trace_derives_formula.
Lemma substitution_computation_formula_correct M rho f b c n k t v :
  holds M rho (substitution_computation_formula f b c n k t v) <->
  substitution_computation M (evalM M rho f) (evalM M rho b) (evalM M rho c)
    (evalM M rho n) (evalM M rho k) (evalM M rho t) (evalM M rho v).
Proof.
  unfold substitution_computation_formula,substitution_computation.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite tuple7_formula_correct. setoid_rewrite trace_derives_formula_correct.
  unfold evalM. now setoid_rewrite eval_up.
Qed.

Lemma substitution_computation_leaf M f b c n k t v :
  substitution_leaf M f b c n k t v -> substitution_computation M f b c n k t v.
Proof.
  intro H. destruct (tuple7_total M f b c n k t v) as [r Hr].
  exists r. split; [exact Hr|]. apply trace_derives_base.
  apply substitution_rule_base. exists f,b,c,n,k,t,v. auto.
Qed.

Lemma substitution_computation_binary M h a d f b c n k t x y v :
  sf_binary h -> sf_relation M h a d f ->
  substitution_computation M a b c n k t x -> substitution_computation M d b c n k t y ->
  substitution_binary M h x y v -> substitution_computation M f b c n k t v.
Proof.
  intros Hh Hf [p [Hp Hdp]] [q [Hq Hdq]] Hv.
  destruct (tuple7_total M f b c n k t v) as [r Hr].
  exists r. split; [exact Hr|]. apply (trace_derives_binary M substitution_rules r p q Hdp Hdq).
  apply substitution_rule_binary. exists f,b,c,n,k,t,v. split; [exact Hr|].
  assert (Hcase : substitution_binary_case M h f b c n k t v p q).
  { exists a,d,x,y. auto. }
  destruct Hh as [Hh|[Hh|Hh]]; subst h; tauto.
Qed.

Lemma substitution_computation_unary M universal a f b c n k t d e m w v :
  sf_relation M (substitution_source_quantifier universal) a (zeroM M) f ->
  substitution_lift M b c n k d e m ->
  substitution_computation M a d e m (succM M k) t w ->
  substitution_quantifier M universal k t w v -> substitution_computation M f b c n k t v.
Proof.
  intros Hf He [p [Hp Hdp]] Hv.
  destruct (tuple7_total M f b c n k t v) as [r Hr].
  exists r. split; [exact Hr|]. apply (trace_derives_unary M substitution_rules r p Hdp).
  apply substitution_rule_unary. exists f,b,c,n,k,t,v. split; [exact Hr|].
  assert (Hcase : substitution_unary_case M universal f b c n k t v p).
  { exists a,d,e,m,w. auto. }
  destruct universal; tauto.
Qed.

Definition substitution_computation_total_formula : form :=
  ∀∀∀∀∀∃ substitution_computation_formula $6 $5 $4 $3 $2 $1 $0.

Lemma substitution_computation_total_definable M : Definable1 M
  (fun f => forall b c n k t, exists v, substitution_computation M f b c n k t v).
Proof.
  exists substitution_computation_total_formula,(fun _ => zeroM M).
  intro f. unfold substitution_computation_total_formula.
  repeat setoid_rewrite holds_all. setoid_rewrite holds_ex.
  setoid_rewrite substitution_computation_formula_correct. reflexivity.
Qed.

Theorem substitution_computation_total M f b c n k t :
  exists v, substitution_computation M f b c n k t v.
Proof.
  revert f b c n k t. apply (sf_code_induction M
    (fun f => forall b c n k t, exists v, substitution_computation M f b c n k t v)).
  - apply substitution_computation_total_definable.
  - intros b c n k t. exists (zeroM M). apply substitution_computation_leaf.
    left. auto.
  - intros f Hbad b c n k t. exists (zeroM M). apply substitution_computation_leaf.
    left. auto.
  - intros a d f Hf b c n k t.
    destruct (substitution_lookup_total M b c n k a) as [x Hx].
    destruct (substitution_lookup_total M b c n k d) as [y Hy].
    destruct (substitution_atom_total M false x y t k) as [v Hv].
    exists v. apply substitution_computation_leaf. right; left. exists a,d,x,y. auto.
  - intros a d f Hf b c n k t.
    destruct (substitution_lookup_total M b c n k a) as [x Hx].
    destruct (substitution_lookup_total M b c n k d) as [y Hy].
    destruct (substitution_atom_total M true x y t k) as [v Hv].
    exists v. apply substitution_computation_leaf. right; right. exists a,d,x,y. auto.
  - intros h a d f Hh Hf IHa IHd b c n k t.
    destruct (IHa b c n k t) as [x Hx]. destruct (IHd b c n k t) as [y Hy].
    destruct (substitution_binary_total M h x y) as [v Hv].
    exists v. exact (substitution_computation_binary M h a d f b c n k t x y v Hh Hf Hx Hy Hv).
  - intros h a f Hh Hf IHa b c n k t.
    destruct (substitution_lift_total M b c n k) as [d [e [m He]]].
    destruct (IHa d e m (succM M k) t) as [w Hw].
    destruct Hh as [Hh|Hh]; subst h.
    + destruct (substitution_quantifier_total M true k t w) as [v Hv].
      exists v. exact (substitution_computation_unary M true a f b c n k t d e m w v Hf He Hw Hv).
    + destruct (substitution_quantifier_total M false k t w) as [v Hv].
      exists v. exact (substitution_computation_unary M false a f b c n k t d e m w v Hf He Hw Hv).
Qed.

Lemma substitution_computation_formula_bound :
  bounded 7 (substitution_computation_formula $0 $1 $2 $3 $4 $5 $6).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Print Assumptions substitution_computation_formula_correct.
Print Assumptions substitution_computation_leaf.
Print Assumptions substitution_computation_binary.
Print Assumptions substitution_computation_unary.
Print Assumptions substitution_computation_total.
Print Assumptions substitution_computation_formula_bound.
