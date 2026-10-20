(** An internally certified translation from full de Bruijn source codes
    into the guarded named quotient language. The existence proof uses PA
    induction on source codes uniformly over all encoded environments. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  NumericalProofs SentenceBounds SetFormulaCodes SetCodeDescent
  NumericalEnvironments CodeTuples QuotationPayloads NumericalTraces QuotationRules.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition numerical_quotation M f b c n k t v := exists r,
  tuple7_graph M f b c n k t v r /\ trace_derives M quotation_rules r.
Definition numerical_quotation_formula (f b c n k t v : term) : form :=
  ∃ (tuple7_formula f`[↑] b`[↑] c`[↑] n`[↑] k`[↑] t`[↑] v`[↑] $0 ∧
    trace_derives_formula quotation_rules $0).

Local Opaque holds tuple7_formula trace_derives_formula.
Lemma numerical_quotation_formula_correct M rho f b c n k t v :
  holds M rho (numerical_quotation_formula f b c n k t v) <->
  numerical_quotation M (evalM M rho f) (evalM M rho b) (evalM M rho c)
    (evalM M rho n) (evalM M rho k) (evalM M rho t) (evalM M rho v).
Proof.
  unfold numerical_quotation_formula,numerical_quotation.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite tuple7_formula_correct. setoid_rewrite trace_derives_formula_correct.
  unfold evalM. now setoid_rewrite eval_up.
Qed.

Lemma numerical_quotation_leaf M f b c n k t v :
  quotation_leaf M f b c n k t v -> numerical_quotation M f b c n k t v.
Proof.
  intro H. destruct (tuple7_total M f b c n k t v) as [r Hr].
  exists r. split; [exact Hr|]. apply trace_derives_base.
  apply quotation_rule_base. exists f,b,c,n,k,t,v. auto.
Qed.

Lemma numerical_quotation_binary M h a d f b c n k t x y v :
  sf_binary h -> sf_relation M h a d f ->
  numerical_quotation M a b c n k t x -> numerical_quotation M d b c n k t y ->
  quotation_binary M h x y v -> numerical_quotation M f b c n k t v.
Proof.
  intros Hh Hf [p [Hp Hdp]] [q [Hq Hdq]] Hv.
  destruct (tuple7_total M f b c n k t v) as [r Hr].
  exists r. split; [exact Hr|]. apply (trace_derives_binary M quotation_rules r p q Hdp Hdq).
  apply quotation_rule_binary. exists f,b,c,n,k,t,v. split; [exact Hr|].
  assert (Hcase : quotation_binary_case M h f b c n k t v p q).
  { exists a,d,x,y. auto. }
  destruct Hh as [Hh|[Hh|Hh]]; subst h; tauto.
Qed.

Lemma numerical_quotation_unary M universal a f b c n k t d e m w v :
  sf_relation M (quotation_source_quantifier universal) a (zeroM M) f ->
  environment_cons M b c n k d e m ->
  numerical_quotation M a d e m (succM M k) t w ->
  quotation_quantifier M universal k t w v -> numerical_quotation M f b c n k t v.
Proof.
  intros Hf He [p [Hp Hdp]] Hv.
  destruct (tuple7_total M f b c n k t v) as [r Hr].
  exists r. split; [exact Hr|]. apply (trace_derives_unary M quotation_rules r p Hdp).
  apply quotation_rule_unary. exists f,b,c,n,k,t,v. split; [exact Hr|].
  assert (Hcase : quotation_unary_case M universal f b c n k t v p).
  { exists a,d,e,m,w. auto. }
  destruct universal; tauto.
Qed.

Definition numerical_quotation_total_formula : form :=
  ∀∀∀∀∀∃ numerical_quotation_formula $6 $5 $4 $3 $2 $1 $0.

Lemma numerical_quotation_total_definable M : Definable1 M
  (fun f => forall b c n k t, exists v, numerical_quotation M f b c n k t v).
Proof.
  exists numerical_quotation_total_formula,(fun _ => zeroM M).
  intro f. unfold numerical_quotation_total_formula.
  repeat setoid_rewrite holds_all. setoid_rewrite holds_ex.
  setoid_rewrite numerical_quotation_formula_correct. reflexivity.
Qed.

Theorem numerical_quotation_total M f b c n k t :
  exists v, numerical_quotation M f b c n k t v.
Proof.
  revert f b c n k t. apply (sf_code_induction M
    (fun f => forall b c n k t, exists v, numerical_quotation M f b c n k t v)).
  - apply numerical_quotation_total_definable.
  - intros b c n k t. exists (code_numeral M 1). apply numerical_quotation_leaf.
    left. auto.
  - intros f Hbad b c n k t. exists (code_numeral M 1). apply numerical_quotation_leaf.
    left. auto.
  - intros a d f Hf b c n k t.
    destruct (environment_lookup_total M b c n a) as [x Hx].
    destruct (environment_lookup_total M b c n d) as [y Hy].
    destruct (quotation_atom_total M false x y t k) as [v Hv].
    exists v. apply numerical_quotation_leaf. right; left. exists a,d,x,y. auto.
  - intros a d f Hf b c n k t.
    destruct (environment_lookup_total M b c n a) as [x Hx].
    destruct (environment_lookup_total M b c n d) as [y Hy].
    destruct (quotation_atom_total M true x y t k) as [v Hv].
    exists v. apply numerical_quotation_leaf. right; right. exists a,d,x,y. auto.
  - intros h a d f Hh Hf IHa IHd b c n k t.
    destruct (IHa b c n k t) as [x Hx]. destruct (IHd b c n k t) as [y Hy].
    destruct (quotation_binary_total M h x y) as [v Hv].
    exists v. exact (numerical_quotation_binary M h a d f b c n k t x y v Hh Hf Hx Hy Hv).
  - intros h a f Hh Hf IHa b c n k t.
    destruct (environment_cons_total M b c n k) as [d [e [m He]]].
    destruct (IHa d e m (succM M k) t) as [w Hw].
    destruct Hh as [Hh|Hh]; subst h.
    + destruct (quotation_quantifier_total M true k t w) as [v Hv].
      exists v. exact (numerical_quotation_unary M true a f b c n k t d e m w v Hf He Hw Hv).
    + destruct (quotation_quantifier_total M false k t w) as [v Hv].
      exists v. exact (numerical_quotation_unary M false a f b c n k t d e m w v Hf He Hw Hv).
Qed.

Lemma numerical_quotation_formula_bound :
  bounded 7 (numerical_quotation_formula $0 $1 $2 $3 $4 $5 $6).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Print Assumptions numerical_quotation_formula_correct.
Print Assumptions numerical_quotation_leaf.
Print Assumptions numerical_quotation_binary.
Print Assumptions numerical_quotation_unary.
Print Assumptions numerical_quotation_total.
Print Assumptions numerical_quotation_formula_bound.
