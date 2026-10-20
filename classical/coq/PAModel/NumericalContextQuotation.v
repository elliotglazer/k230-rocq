(** Pointwise quotation of exact-length source contexts. Source code zero is
    a real falsity entry and quotes to target code one; no padding is a member. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula
  CodeExpressions NumericalProofs NumericalEnvironments NumericalContexts InternalRecursion
  BetaExtension ProofClosure NumericalQuotation QuotationFunctionality SentenceBounds.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition context_quotation M b c n p q m fresh domain d e :=
  forall i f g, coding_lt M i n -> beta M b c i f -> beta M d e i g ->
    numerical_quotation M f p q m fresh domain g.

Definition quotation_context_lift3 (t : term) : term :=
  context_lift (context_lift (context_lift t)).
Lemma quotation_context_eval_lift3 M rho x y z t :
  evalM M (x .: y .: z .: rho) (quotation_context_lift3 t) = evalM M rho t.
Proof. unfold quotation_context_lift3. now rewrite !context_eval_lift. Qed.

(** Under three binders: i=$2, source entry f=$1, target entry g=$0. *)
Definition context_quotation_formula (b c n p q m fresh domain d e : term) : form :=
  ∀∀∀ (Peano.sless $2 (quotation_context_lift3 n) →
    beta_formula (quotation_context_lift3 b) (quotation_context_lift3 c) $2 $1 →
    beta_formula (quotation_context_lift3 d) (quotation_context_lift3 e) $2 $0 →
    numerical_quotation_formula $1 (quotation_context_lift3 p) (quotation_context_lift3 q)
      (quotation_context_lift3 m) (quotation_context_lift3 fresh)
      (quotation_context_lift3 domain) $0).

Local Opaque holds beta_formula numerical_quotation_formula.
Theorem context_quotation_formula_correct M rho b c n p q m fresh domain d e :
  holds M rho (context_quotation_formula b c n p q m fresh domain d e) <->
  context_quotation M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho p) (evalM M rho q) (evalM M rho m) (evalM M rho fresh)
    (evalM M rho domain) (evalM M rho d) (evalM M rho e).
Proof.
  unfold context_quotation_formula,context_quotation.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_sless. setoid_rewrite beta_formula_correct.
  setoid_rewrite numerical_quotation_formula_correct.
  setoid_rewrite quotation_context_eval_lift3. reflexivity.
Qed.

(** The quoted entry is independent of the accumulating output table.
    Before the existential binder, slots are g,i,out-mod,out-div,b,c,p,q,m,fresh,domain. *)
Definition context_quotation_step_formula : form :=
  ∃ (beta_formula $5 $6 $2 $0 ∧ numerical_quotation_formula $0 $7 $8 $9 $10 $11 $1).

Lemma context_quotation_step_correct M b c p q m fresh domain d e i g :
  recursion_step M context_quotation_step_formula
    (b .: c .: p .: q .: m .: fresh .: domain .: fun _ => zeroM M) d e i g <->
  exists f, beta M b c i f /\ numerical_quotation M f p q m fresh domain g.
Proof.
  unfold recursion_step,context_quotation_step_formula.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite beta_formula_correct. setoid_rewrite numerical_quotation_formula_correct.
  reflexivity.
Qed.

Theorem context_quotation_total M b c n p q m fresh domain :
  exists d e, context_quotation M b c n p q m fresh domain d e.
Proof.
  assert (Ht : forall d e i, exists g, recursion_step M context_quotation_step_formula
    (b .: c .: p .: q .: m .: fresh .: domain .: fun _ => zeroM M) d e i g).
  { intros d e i. destruct (beta_total M b c i) as [f Hf].
    destruct (numerical_quotation_total M f p q m fresh domain) as [g Hg].
    exists g. apply context_quotation_step_correct. exists f. auto. }
  assert (Hp : forall d e d' e' i, prefix M d e d' e' i -> forall g,
    (recursion_step M context_quotation_step_formula
      (b .: c .: p .: q .: m .: fresh .: domain .: fun _ => zeroM M) d e i g <->
     recursion_step M context_quotation_step_formula
      (b .: c .: p .: q .: m .: fresh .: domain .: fun _ => zeroM M) d' e' i g)).
  { intros. rewrite !context_quotation_step_correct. reflexivity. }
  destruct (recursion_table_total M context_quotation_step_formula
    (b .: c .: p .: q .: m .: fresh .: domain .: fun _ => zeroM M) Ht Hp n)
    as [d [e Hde]].
  exists d,e. intros i f g Hi Hf Hg.
  pose proof (Hde i g Hi Hg) as Hr.
  apply context_quotation_step_correct in Hr as [f' [Hf' Hr]].
  assert (f=f') by (eapply beta_unique; eassumption). now subst f'.
Qed.

Theorem context_quotation_empty M b c p q m fresh domain d e :
  context_quotation M b c (zeroM M) p q m fresh domain d e.
Proof. intros i f g Hi. exfalso. exact (coding_not_lt_zero M i Hi). Qed.

Theorem context_quotation_functional M b c n p q m fresh domain d e d' e' :
  context_quotation M b c n p q m fresh domain d e ->
  context_quotation M b c n p q m fresh domain d' e' ->
  forall i g g', coding_lt M i n -> beta M d e i g -> beta M d' e' i g' -> g=g'.
Proof.
  intros H H' i g g' Hi Hg Hg'. destruct (beta_total M b c i) as [f Hf].
  exact (numerical_quotation_functional M f p q m fresh domain g g'
    (H i f g Hi Hf Hg) (H' i f g' Hi Hf Hg')).
Qed.

Theorem context_quotation_member_forward M b c n p q m fresh domain d e f :
  context_quotation M b c n p q m fresh domain d e -> context_member M b c n f ->
  exists g, context_member M d e n g /\ numerical_quotation M f p q m fresh domain g.
Proof.
  intros H [i [Hi Hf]]. destruct (beta_total M d e i) as [g Hg].
  exists g. split; [exists i;auto|exact (H i f g Hi Hf Hg)].
Qed.

Theorem context_quotation_member_iff M b c n p q m fresh domain d e g :
  context_quotation M b c n p q m fresh domain d e ->
  (context_member M d e n g <->
   exists f, context_member M b c n f /\ numerical_quotation M f p q m fresh domain g).
Proof.
  intro H. split.
  - intros [i [Hi Hg]]. destruct (beta_total M b c i) as [f Hf].
    exists f. split; [exists i;auto|exact (H i f g Hi Hf Hg)].
  - intros [f [Hf Hq]].
    destruct (context_quotation_member_forward M b c n p q m fresh domain d e f H Hf)
      as [g' [Hg' Hq']].
    assert (g'=g) by (eapply numerical_quotation_functional; eassumption). now subst g'.
Qed.

Theorem context_quotation_falsity_entry M b c n p q m fresh domain d e i g :
  context_quotation M b c n p q m fresh domain d e ->
  coding_lt M i n -> beta M b c i (zeroM M) -> beta M d e i g ->
  g=code_numeral M 1.
Proof.
  intros H Hi Hf Hg. apply (numerical_quotation_invalid M (zeroM M) p q m fresh domain g).
  - now left.
  - exact (H i (zeroM M) g Hi Hf Hg).
Qed.

Theorem context_quotation_falsity_member M b c n p q m fresh domain d e :
  context_quotation M b c n p q m fresh domain d e ->
  context_member M b c n (zeroM M) -> context_member M d e n (code_numeral M 1).
Proof.
  intros H Hf.
  destruct (context_quotation_member_forward M b c n p q m fresh domain d e (zeroM M) H Hf)
    as [g [Hg Hq]].
  assert (g=code_numeral M 1) by
    exact (numerical_quotation_invalid M (zeroM M) p q m fresh domain g (or_introl eq_refl) Hq).
  now subst g.
Qed.

Theorem context_quotation_empty_has_no_members M b c p q m fresh domain d e g :
  context_quotation M b c (zeroM M) p q m fresh domain d e ->
  ~context_member M d e (zeroM M) g.
Proof. intros _. apply context_empty. Qed.

Theorem context_quotation_cons M b c n p q m fresh domain d e f g b' c' n' d' e' :
  context_quotation M b c n p q m fresh domain d e ->
  numerical_quotation M f p q m fresh domain g ->
  environment_cons M b c n f b' c' n' -> environment_cons M d e n g d' e' n' ->
  context_quotation M b' c' n' p q m fresh domain d' e'.
Proof.
  intros Hq Hfg Hs Ht i x y Hi Hx Hy. pose proof (proj1 Hs) as En.
  apply (proj2 (environment_lookup_inside M b' c' n' i x Hi)) in Hx.
  apply (proj2 (environment_lookup_inside M d' e' n' i y Hi)) in Hy.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i) as [E|[j E]]; subst i.
  - apply (proj1 (environment_cons_head M b c n f b' c' n' x Hs)) in Hx.
    apply (proj1 (environment_cons_head M d e n g d' e' n' y Ht)) in Hy.
    now subst x y.
  - apply (proj1 (environment_cons_tail M b c n f b' c' n' j x Hs)) in Hx.
    apply (proj1 (environment_cons_tail M d e n g d' e' n' j y Ht)) in Hy.
    rewrite En in Hi. apply (proj1 (coding_lt_succ_cancel M j n)) in Hi.
    apply (Hq j x y Hi).
    + exact (proj1 (environment_lookup_inside M b c n j x Hi) Hx).
    + exact (proj1 (environment_lookup_inside M d e n j y Hi) Hy).
Qed.

Theorem context_quotation_formula_bound :
  bounded 10 (context_quotation_formula $0 $1 $2 $3 $4 $5 $6 $7 $8 $9).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
