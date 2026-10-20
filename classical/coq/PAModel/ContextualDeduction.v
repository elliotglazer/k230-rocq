(** Discharge of one local assumption from an internally coded target proof.
    Proof lengths and every formula/context code range over the PA model. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  NumericalTraces NumericalContexts NumericalEnvironments FreshNames
  ContextualProofs ContextualLogic.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Theorem context_fresh_cons M b c n h d e m x :
  environment_cons M b c n h d e m ->
  (context_fresh M d e m x <-> formula_fresh M h x /\ context_fresh M b c n x).
Proof.
  intro Hcons. split.
  - intro H. split.
    + apply H. apply (proj2 (context_member_cons M b c n h d e m h Hcons)). now left.
    + intros a Ha. apply H. apply (proj2 (context_member_cons M b c n h d e m a Hcons)). now right.
  - intros [Hh HG] a Ha. apply (proj1 (context_member_cons M b c n h d e m a Hcons)) in Ha.
    destruct Ha as [->|Ha]; [exact Hh|exact (HG a Ha)].
Qed.

Definition contextual_deduction_at M b c n d e m h r := forall a,
  contextual_row M d e m a r ->
  exists ha, implication_graph M h a ha /\ contextually_provable M b c n ha.

Definition contextual_deduction_formula (b c n d e m h r : term) : form :=
  ∀ (contextual_row_formula d`[↑] e`[↑] m`[↑] $0 r`[↑] →
    ∃ (implication_formula h`[↑]`[↑] $1 $0 ∧
      contextually_provable_formula b`[↑]`[↑] c`[↑]`[↑] n`[↑]`[↑] $0)).

Local Opaque holds contextual_row_formula implication_formula contextually_provable_formula.
Lemma contextual_deduction_formula_correct M rho b c n d e m h r :
  holds M rho (contextual_deduction_formula b c n d e m h r) <->
  contextual_deduction_at M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho d) (evalM M rho e) (evalM M rho m) (evalM M rho h) (evalM M rho r).
Proof.
  unfold contextual_deduction_formula,contextual_deduction_at.
  setoid_rewrite holds_all. setoid_rewrite holds_imp. setoid_rewrite holds_ex.
  setoid_rewrite holds_and. setoid_rewrite contextual_row_formula_correct.
  setoid_rewrite implication_formula_correct. setoid_rewrite contextually_provable_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Lemma contextual_deduction_definable M b c n d e m h :
  Definable1 M (contextual_deduction_at M b c n d e m h).
Proof.
  exists (contextual_deduction_formula $1 $2 $3 $4 $5 $6 $7 $0),
    (b .: c .: n .: d .: e .: m .: h .: fun _ => zeroM M).
  intro r. symmetry. apply contextual_deduction_formula_correct.
Qed.

Theorem contextual_deduction M b c n h d e m f :
  environment_cons M b c n h d e m -> contextually_provable M d e m f ->
  exists hf, implication_graph M h f hf /\ contextually_provable M b c n hf.
Proof.
  intros Hcons [r [Hr HD]].
  assert (HP : contextual_deduction_at M b c n d e m h r).
  { apply (trace_derives_induction M contextual_rules
      (contextual_deduction_at M b c n d e m h)).
    - apply contextual_deduction_definable.
    - intros s Hbase a Hs.
      apply contextual_rule_base in Hbase as [b0 [c0 [n0 [a0 [Hs0 Hbase]]]]].
      destruct (contextual_row_injective M d e m a b0 c0 n0 a0 s Hs Hs0)
        as [Eb [Ec [En Ea]]]. subst b0 c0 n0 a0.
      destruct Hbase as [Hglobal|Ha].
      + apply contextual_implication_intro,contextual_global,Hglobal.
      + apply (proj1 (context_member_cons M b c n h d e m a Hcons)) in Ha.
        destruct Ha as [Ea|Ha].
        * subst a. apply contextual_identity.
        * apply contextual_implication_intro,contextual_hyp,Ha.
    - intros s p IH Hstep a Hs.
      apply contextual_rule_unary in Hstep as [b0 [c0 [n0 [x [a0 [g [Hs0 [Hp [Hall Hfresh]]]]]]]]].
      destruct (contextual_row_injective M d e m a b0 c0 n0 g s Hs Hs0)
        as [Eb [Ec [En Ea]]]. subst b0 c0 n0 g.
      destruct (IH a0 Hp) as [ha [Hha Hproof]].
      apply (proj1 (context_fresh_cons M b c n h d e m x Hcons)) in Hfresh.
      destruct Hfresh as [Hh HG].
      exact (contextual_generalization_under_hypothesis M b c n x h a0 ha a
        HG Hh Hha Hall Hproof).
    - intros s p q IHp IHq Hstep a Hs.
      apply contextual_rule_binary in Hstep as [b0 [c0 [n0 [a0 [g [ag [Hs0 [Hp [Hq Himp]]]]]]]]].
      destruct (contextual_row_injective M d e m a b0 c0 n0 g s Hs Hs0)
        as [Eb [Ec [En Ea]]]. subst b0 c0 n0 g.
      destruct (IHp a0 Hp) as [ha [Hha Hpa]].
      destruct (IHq ag Hq) as [hag [Hhag Hpag]].
      exact (contextual_deduction_mp M b c n h a0 a ag ha hag Himp Hha Hhag Hpa Hpag).
    - exact HD. }
  exact (HP f Hr).
Qed.

Print Assumptions context_fresh_cons.
Print Assumptions contextual_deduction_formula_correct.
Print Assumptions contextual_deduction.
