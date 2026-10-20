(** Internally finite target derivations with local assumptions.  Global K
    theorems may be used as leaves. Generalization requires freshness in every
    local assumption; it is not the unrestricted rule of a theory extension. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofClosure CodeTuples NumericalTraces NumericalContexts FreshNames SentenceBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition context_fresh M b c n x :=
  forall f, context_member M b c n f -> formula_fresh M f x.
Definition context_fresh_formula (b c n x : term) : form :=
  ∀ (context_member_formula b`[↑] c`[↑] n`[↑] $0 →
    formula_fresh_formula $0 x`[↑]).
Local Opaque holds context_member_formula formula_fresh_formula.
Lemma context_fresh_formula_correct M rho b c n x :
  holds M rho (context_fresh_formula b c n x) <->
  context_fresh M (evalM M rho b) (evalM M rho c) (evalM M rho n) (evalM M rho x).
Proof.
  unfold context_fresh_formula,context_fresh.
  setoid_rewrite holds_all. setoid_rewrite holds_imp.
  setoid_rewrite context_member_formula_correct.
  setoid_rewrite formula_fresh_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Definition contextual_row M b c n f r :=
  tuple7_graph M (zeroM M) b c n f (zeroM M) (zeroM M) r.
Definition contextual_row_formula (b c n f r : term) : form :=
  tuple7_formula zero b c n f zero zero r.
Lemma contextual_row_formula_correct M rho b c n f r :
  holds M rho (contextual_row_formula b c n f r) <->
  contextual_row M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho f) (evalM M rho r).
Proof. apply tuple7_formula_correct. Qed.
Lemma contextual_row_total M b c n f : exists r, contextual_row M b c n f r.
Proof. apply tuple7_total. Qed.
Lemma contextual_row_injective M b c n f b' c' n' f' r :
  contextual_row M b c n f r -> contextual_row M b' c' n' f' r ->
  b=b' /\ c=c' /\ n=n' /\ f=f'.
Proof.
  intros H H'. destruct (tuple7_injective M _ _ _ _ _ _ _ _ _ _ _ _ _ _ r H H')
    as [_ [Hb [Hc [Hn [Hf _]]]]]. auto.
Qed.

Definition contextual_base M r := exists b c n f,
  contextual_row M b c n f r /\
  (numerically_provable M f \/ context_member M b c n f).
Definition contextual_unary M r p := exists b c n x f g,
  contextual_row M b c n g r /\ contextual_row M b c n f p /\
  universal_graph M x f g /\ context_fresh M b c n x.
Definition contextual_binary M r p q := exists b c n f g h,
  contextual_row M b c n g r /\ contextual_row M b c n f p /\
  contextual_row M b c n h q /\ implication_graph M f g h.

Definition contextual_base_formula : form := ∃∃∃∃
  (contextual_row_formula $3 $2 $1 $0 $4 ∧
   (numerically_provable_formula $0 ∨ context_member_formula $3 $2 $1 $0)).
Definition contextual_unary_formula : form := ∃∃∃∃∃∃
  (contextual_row_formula $5 $4 $3 $0 $6 ∧
   (contextual_row_formula $5 $4 $3 $1 $7 ∧
   (universal_formula $2 $1 $0 ∧ context_fresh_formula $5 $4 $3 $2))).
Definition contextual_binary_formula : form := ∃∃∃∃∃∃
  (contextual_row_formula $5 $4 $3 $1 $6 ∧
   (contextual_row_formula $5 $4 $3 $2 $7 ∧
   (contextual_row_formula $5 $4 $3 $0 $8 ∧ implication_formula $2 $1 $0))).

Local Opaque contextual_row_formula numerically_provable_formula
  universal_formula implication_formula context_fresh_formula.
Lemma contextual_base_formula_correct M rho :
  holds M rho contextual_base_formula <-> contextual_base M (rho 0).
Proof.
  unfold contextual_base_formula,contextual_base. repeat setoid_rewrite holds_ex.
  setoid_rewrite holds_and. setoid_rewrite holds_or.
  setoid_rewrite contextual_row_formula_correct.
  setoid_rewrite numerically_provable_formula_correct.
  setoid_rewrite context_member_formula_correct. reflexivity.
Qed.
Lemma contextual_unary_formula_correct M rho :
  holds M rho contextual_unary_formula <-> contextual_unary M (rho 0) (rho 1).
Proof.
  unfold contextual_unary_formula,contextual_unary. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite contextual_row_formula_correct.
  setoid_rewrite universal_formula_correct. setoid_rewrite context_fresh_formula_correct.
  reflexivity.
Qed.
Lemma contextual_binary_formula_correct M rho :
  holds M rho contextual_binary_formula <-> contextual_binary M (rho 0) (rho 1) (rho 2).
Proof.
  unfold contextual_binary_formula,contextual_binary. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite contextual_row_formula_correct.
  setoid_rewrite implication_formula_correct. reflexivity.
Qed.

Definition contextual_rules : NumericalRules.
Proof.
  refine {| rule_base_formula := contextual_base_formula;
            rule_unary_formula := contextual_unary_formula;
            rule_binary_formula := contextual_binary_formula |};
    apply formula_boundb_sound; vm_compute; reflexivity.
Defined.
Lemma contextual_rule_base M r : trace_base M contextual_rules r <-> contextual_base M r.
Proof. apply contextual_base_formula_correct. Qed.
Lemma contextual_rule_unary M r p : trace_unary M contextual_rules r p <-> contextual_unary M r p.
Proof. apply contextual_unary_formula_correct. Qed.
Lemma contextual_rule_binary M r p q :
  trace_binary M contextual_rules r p q <-> contextual_binary M r p q.
Proof. apply contextual_binary_formula_correct. Qed.

Definition contextually_provable M b c n f := exists r,
  contextual_row M b c n f r /\ trace_derives M contextual_rules r.
Definition contextually_provable_formula (b c n f : term) : form :=
  ∃ (contextual_row_formula b`[↑] c`[↑] n`[↑] f`[↑] $0 ∧
    trace_derives_formula contextual_rules $0).
Local Opaque trace_derives_formula.
Lemma contextually_provable_formula_correct M rho b c n f :
  holds M rho (contextually_provable_formula b c n f) <->
  contextually_provable M (evalM M rho b) (evalM M rho c) (evalM M rho n) (evalM M rho f).
Proof.
  unfold contextually_provable_formula,contextually_provable.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite contextual_row_formula_correct. setoid_rewrite trace_derives_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem contextual_global M b c n f :
  numerically_provable M f -> contextually_provable M b c n f.
Proof.
  intro H. destruct (contextual_row_total M b c n f) as [r Hr].
  exists r. split; [exact Hr|]. apply trace_derives_base,contextual_rule_base.
  exists b,c,n,f. auto.
Qed.
Theorem contextual_hyp M b c n f :
  context_member M b c n f -> contextually_provable M b c n f.
Proof.
  intro H. destruct (contextual_row_total M b c n f) as [r Hr].
  exists r. split; [exact Hr|]. apply trace_derives_base,contextual_rule_base.
  exists b,c,n,f. auto.
Qed.
Theorem contextual_mp M b c n f g h :
  contextually_provable M b c n f -> contextually_provable M b c n h ->
  implication_graph M f g h -> contextually_provable M b c n g.
Proof.
  intros [p [Hp Hdp]] [q [Hq Hdq]] Himp.
  destruct (contextual_row_total M b c n g) as [r Hr].
  exists r. split; [exact Hr|].
  apply (trace_derives_binary M contextual_rules r p q Hdp Hdq),contextual_rule_binary.
  exists b,c,n,f,g,h. auto.
Qed.
Theorem contextual_gen M b c n x f g :
  context_fresh M b c n x -> contextually_provable M b c n f ->
  universal_graph M x f g -> contextually_provable M b c n g.
Proof.
  intros Hfresh [p [Hp Hdp]] Hall.
  destruct (contextual_row_total M b c n g) as [r Hr].
  exists r. split; [exact Hr|].
  apply (trace_derives_unary M contextual_rules r p Hdp),contextual_rule_unary.
  exists b,c,n,x,f,g. auto.
Qed.

Definition context_globally_proved M b c n :=
  forall f, context_member M b c n f -> numerically_provable M f.
Definition context_globally_proved_formula (b c n : term) : form :=
  ∀ (context_member_formula b`[↑] c`[↑] n`[↑] $0 → numerically_provable_formula $0).
Lemma context_globally_proved_formula_correct M rho b c n :
  holds M rho (context_globally_proved_formula b c n) <->
  context_globally_proved M (evalM M rho b) (evalM M rho c) (evalM M rho n).
Proof.
  unfold context_globally_proved_formula,context_globally_proved.
  setoid_rewrite holds_all. setoid_rewrite holds_imp.
  setoid_rewrite context_member_formula_correct.
  setoid_rewrite numerically_provable_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Definition contextual_sound_at M r := forall b c n f,
  contextual_row M b c n f r -> context_globally_proved M b c n -> numerically_provable M f.
Definition contextual_sound_formula : form := ∀∀∀∀
  (contextual_row_formula $3 $2 $1 $0 $4 →
    context_globally_proved_formula $3 $2 $1 → numerically_provable_formula $0).
Local Opaque context_globally_proved_formula.
Lemma contextual_sound_definable M : Definable1 M (contextual_sound_at M).
Proof.
  exists contextual_sound_formula,(fun _ => zeroM M). intro r.
  unfold contextual_sound_formula,contextual_sound_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite contextual_row_formula_correct.
  setoid_rewrite context_globally_proved_formula_correct.
  setoid_rewrite numerically_provable_formula_correct. reflexivity.
Qed.

Theorem contextual_sound M b c n f :
  context_globally_proved M b c n -> contextually_provable M b c n f -> numerically_provable M f.
Proof.
  intros HG [r [Hr HD]].
  assert (Hsound : contextual_sound_at M r).
  { apply (trace_derives_induction M contextual_rules (contextual_sound_at M)).
    - apply contextual_sound_definable.
    - intros s Hbase b' c' n' f' Hs Hglobal.
      apply contextual_rule_base in Hbase as [b0 [c0 [n0 [f0 [Hs0 Hbase]]]]].
      destruct (contextual_row_injective M b' c' n' f' b0 c0 n0 f0 s Hs Hs0)
        as [-> [-> [-> ->]]]. destruct Hbase; auto.
    - intros s p IH Hstep b' c' n' f' Hs Hglobal.
      apply contextual_rule_unary in Hstep as [b0 [c0 [n0 [x [a [g [Hs0 [Hp [Hall Hfresh]]]]]]]]].
      destruct (contextual_row_injective M b' c' n' f' b0 c0 n0 g s Hs Hs0)
        as [-> [-> [-> ->]]].
      exact (numerical_gen M x a g (IH b0 c0 n0 a Hp Hglobal) Hall).
    - intros s p q IHp IHq Hstep b' c' n' f' Hs Hglobal.
      apply contextual_rule_binary in Hstep as [b0 [c0 [n0 [a [g [h [Hs0 [Hp [Hq Himp]]]]]]]]].
      destruct (contextual_row_injective M b' c' n' f' b0 c0 n0 g s Hs Hs0)
        as [-> [-> [-> ->]]].
      exact (numerical_mp M a g h (IHp b0 c0 n0 a Hp Hglobal)
        (IHq b0 c0 n0 h Hq Hglobal) Himp).
    - exact HD. }
  exact (Hsound b c n f Hr HG).
Qed.

Corollary contextual_empty_iff M b c f :
  contextually_provable M b c (zeroM M) f <-> numerically_provable M f.
Proof.
  split; [|apply contextual_global]. apply contextual_sound.
  intros a Ha. exfalso. exact (context_empty M b c a Ha).
Qed.

Print Assumptions context_fresh_formula_correct.
Print Assumptions contextually_provable_formula_correct.
Print Assumptions contextual_global.
Print Assumptions contextual_hyp.
Print Assumptions contextual_mp.
Print Assumptions contextual_gen.
Print Assumptions contextual_sound.
Print Assumptions contextual_empty_iff.

