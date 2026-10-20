(** Pointwise renaming of exact-length source contexts. All lengths, indices,
    formula codes, and map parameters range over the arbitrary PA model. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula
  NumericalProofs NumericalEnvironments NumericalContexts InternalRecursion BetaExtension ProofClosure
  NumericalRenamingMaps NumericalRenaming SourceRenamingBounds SourceBounded SentenceBounds.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition context_renaming M b c n p q m delta d e :=
  forall i f g, coding_lt M i n -> beta M b c i f -> beta M d e i g ->
    numerical_renaming M f p q m delta g.

Definition context_lift3 (t : term) : term := context_lift (context_lift (context_lift t)).
Lemma context_eval_lift3 M rho x y z t :
  evalM M (x .: y .: z .: rho) (context_lift3 t) = evalM M rho t.
Proof. unfold context_lift3. now rewrite !context_eval_lift. Qed.

Definition context_renaming_formula (b c n p q m delta d e : term) : form :=
  ∀∀∀ (Peano.sless $2 (context_lift3 n) →
    beta_formula (context_lift3 b) (context_lift3 c) $2 $1 →
    beta_formula (context_lift3 d) (context_lift3 e) $2 $0 →
    numerical_renaming_formula $1 (context_lift3 p) (context_lift3 q)
      (context_lift3 m) (context_lift3 delta) $0).

Local Opaque holds beta_formula numerical_renaming_formula.
Theorem context_renaming_formula_correct M rho b c n p q m delta d e :
  holds M rho (context_renaming_formula b c n p q m delta d e) <->
  context_renaming M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho p) (evalM M rho q) (evalM M rho m) (evalM M rho delta)
    (evalM M rho d) (evalM M rho e).
Proof.
  unfold context_renaming_formula,context_renaming.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_sless. setoid_rewrite beta_formula_correct.
  setoid_rewrite numerical_renaming_formula_correct.
  setoid_rewrite context_eval_lift3. reflexivity.
Qed.

(** The recursion theorem internally packs successive values with beta_extension.
    The step does not inspect any part of its accumulating output table. *)
Definition context_renaming_step_formula : form :=
  ∃ (beta_formula $5 $6 $2 $0 ∧ numerical_renaming_formula $0 $7 $8 $9 $10 $1).

Lemma context_renaming_step_correct M b c p q m delta d e i g :
  recursion_step M context_renaming_step_formula
    (b .: c .: p .: q .: m .: delta .: fun _ => zeroM M) d e i g <->
  exists f, beta M b c i f /\ numerical_renaming M f p q m delta g.
Proof.
  unfold recursion_step,context_renaming_step_formula.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite beta_formula_correct. setoid_rewrite numerical_renaming_formula_correct.
  reflexivity.
Qed.

Theorem context_renaming_total M b c n p q m delta :
  exists d e, context_renaming M b c n p q m delta d e.
Proof.
  assert (Ht : forall d e i, exists g, recursion_step M context_renaming_step_formula
    (b .: c .: p .: q .: m .: delta .: fun _ => zeroM M) d e i g).
  { intros d e i. destruct (beta_total M b c i) as [f Hf].
    destruct (numerical_renaming_total M f p q m delta) as [g Hg].
    exists g. apply context_renaming_step_correct. exists f. auto. }
  assert (Hp : forall d e d' e' i, prefix M d e d' e' i -> forall g,
    (recursion_step M context_renaming_step_formula
      (b .: c .: p .: q .: m .: delta .: fun _ => zeroM M) d e i g <->
     recursion_step M context_renaming_step_formula
      (b .: c .: p .: q .: m .: delta .: fun _ => zeroM M) d' e' i g)).
  { intros. rewrite !context_renaming_step_correct. reflexivity. }
  destruct (recursion_table_total M context_renaming_step_formula
    (b .: c .: p .: q .: m .: delta .: fun _ => zeroM M) Ht Hp n) as [d [e Hde]].
  exists d,e. intros i f g Hi Hf Hg.
  pose proof (Hde i g Hi Hg) as Hr.
  apply context_renaming_step_correct in Hr as [f' [Hf' Hr]].
  assert (f=f') by (eapply beta_unique; eassumption). now subst f'.
Qed.

Theorem context_renaming_empty M b c p q m delta d e :
  context_renaming M b c (zeroM M) p q m delta d e.
Proof. intros i f g Hi. exfalso. exact (coding_not_lt_zero M i Hi). Qed.

Theorem context_renaming_functional M b c n p q m delta d e d' e' :
  context_renaming M b c n p q m delta d e ->
  context_renaming M b c n p q m delta d' e' ->
  forall i g g', coding_lt M i n -> beta M d e i g -> beta M d' e' i g' -> g=g'.
Proof.
  intros H H' i g g' Hi Hg Hg'. destruct (beta_total M b c i) as [f Hf].
  exact (numerical_renaming_functional M f p q m delta g g'
    (H i f g Hi Hf Hg) (H' i f g' Hi Hf Hg')).
Qed.

Theorem context_renaming_member_forward M b c n p q m delta d e f :
  context_renaming M b c n p q m delta d e -> context_member M b c n f ->
  exists g, context_member M d e n g /\ numerical_renaming M f p q m delta g.
Proof.
  intros H [i [Hi Hf]]. destruct (beta_total M d e i) as [g Hg].
  exists g. split; [exists i;auto|exact (H i f g Hi Hf Hg)].
Qed.

Theorem context_renaming_member_iff M b c n p q m delta d e g :
  context_renaming M b c n p q m delta d e ->
  (context_member M d e n g <->
   exists f, context_member M b c n f /\ numerical_renaming M f p q m delta g).
Proof.
  intro H. split.
  - intros [i [Hi Hg]]. destruct (beta_total M b c i) as [f Hf].
    exists f. split; [exists i;auto|exact (H i f g Hi Hf Hg)].
  - intros [f [Hf Hr]]. destruct (context_renaming_member_forward M b c n p q m delta d e f H Hf)
      as [g' [Hg' Hr']].
    assert (g'=g) by (eapply numerical_renaming_functional; eassumption). now subst g'.
Qed.

Theorem context_renaming_preserves_bound M b c n p q m delta d e k l :
  context_renaming M b c n p q m delta d e -> context_bounded M b c n k ->
  renaming_maps_bound M p q m delta k l -> context_bounded M d e n l.
Proof.
  intros Hr Hb Hmap g Hg.
  apply (proj1 (context_renaming_member_iff M b c n p q m delta d e g Hr)) in Hg.
  destruct Hg as [f [Hf Hfg]].
  exact (numerical_renaming_preserves_bound M f p q m delta g k l (Hb f Hf) Hfg Hmap).
Qed.

Theorem context_renaming_cons M b c n p q m delta d e f g b' c' n' d' e' :
  context_renaming M b c n p q m delta d e -> numerical_renaming M f p q m delta g ->
  environment_cons M b c n f b' c' n' -> environment_cons M d e n g d' e' n' ->
  context_renaming M b' c' n' p q m delta d' e'.
Proof.
  intros Hr Hfg Hs Ht i x y Hi Hx Hy. pose proof (proj1 Hs) as En.
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
    apply (Hr j x y Hi).
    + exact (proj1 (environment_lookup_inside M b c n j x Hi) Hx).
    + exact (proj1 (environment_lookup_inside M d e n j y Hi) Hy).
Qed.

Definition context_shift M b c n d e :=
  context_renaming M b c n (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) d e.

Definition context_shift_formula (b c n d e : term) : form :=
  context_renaming_formula b c n zero zero zero (σ zero) d e.

Theorem context_shift_formula_correct M rho b c n d e :
  holds M rho (context_shift_formula b c n d e) <->
  context_shift M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho d) (evalM M rho e).
Proof. unfold context_shift_formula,context_shift. apply context_renaming_formula_correct. Qed.

Theorem context_shift_lookup M i j :
  renaming_lookup M (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) i j <-> j=succM M i.
Proof.
  rewrite (renaming_lookup_outside M _ _ _ _ i j (coding_not_lt_zero M i)).
  rewrite (Arithmetic.add_comm M i (succM M (zeroM M))), Arithmetic.add_succ,Arithmetic.add_zero. reflexivity.
Qed.

Theorem context_shift_total M b c n : exists d e, context_shift M b c n d e.
Proof. apply context_renaming_total. Qed.

Theorem context_shift_preserves_bound M b c n d e k :
  context_shift M b c n d e -> context_bounded M b c n k ->
  context_bounded M d e n (succM M k).
Proof.
  intros Hr Hb. eapply context_renaming_preserves_bound; [exact Hr|exact Hb|].
  intros i j Hi Hj. apply context_shift_lookup in Hj. subst j.
  exact (proj2 (coding_lt_succ_cancel M i k) Hi).
Qed.

Theorem context_renaming_formula_bound :
  bounded 9 (context_renaming_formula $0 $1 $2 $3 $4 $5 $6 $7 $8).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Theorem context_shift_formula_bound : bounded 5 (context_shift_formula $0 $1 $2 $3 $4).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.


