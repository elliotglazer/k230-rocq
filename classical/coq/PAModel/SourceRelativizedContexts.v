(** Exact-length context mapping by the actual arithmetic relativization
    graph. The construction uses internal finite recursion, including for
    contexts whose lengths and entries are nonstandard. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula
  NumericalProofs NumericalEnvironments NumericalContexts NumericalContextRenaming
  InternalRecursion BetaExtension ProofClosure SourceBounded SentenceBounds
  SourceRelativization SourceRelativizationFunctionality SourceRelativizationBounds.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_context_relativization M dom b c n u v :=
  forall i f g,coding_lt M i n -> beta M b c i f -> beta M u v i g ->
    source_relativization M dom f g.

Definition source_context_relativization_formula (dom b c n u v:term) : form :=
  ∀∀∀ (Peano.sless $2 (context_lift3 n) →
    beta_formula (context_lift3 b) (context_lift3 c) $2 $1 →
    beta_formula (context_lift3 u) (context_lift3 v) $2 $0 →
    source_relativization_formula (context_lift3 dom) $1 $0).

Local Opaque holds beta_formula source_relativization_formula.
Theorem source_context_relativization_formula_correct M rho dom b c n u v :
  holds M rho (source_context_relativization_formula dom b c n u v) <->
  source_context_relativization M (evalM M rho dom) (evalM M rho b) (evalM M rho c)
    (evalM M rho n) (evalM M rho u) (evalM M rho v).
Proof.
  unfold source_context_relativization_formula,source_context_relativization.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_sless. setoid_rewrite beta_formula_correct.
  setoid_rewrite source_relativization_formula_correct.
  setoid_rewrite context_eval_lift3. reflexivity.
Qed.

Definition source_context_relativization_step : form :=
  ∃ (beta_formula $5 $6 $2 $0 ∧ source_relativization_formula $7 $0 $1).

Lemma source_context_relativization_step_correct M dom b c u v i g :
  recursion_step M source_context_relativization_step
    (b .: c .: dom .: fun _=>zeroM M) u v i g <->
  exists f,beta M b c i f /\ source_relativization M dom f g.
Proof.
  unfold recursion_step,source_context_relativization_step.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite beta_formula_correct. setoid_rewrite source_relativization_formula_correct.
  reflexivity.
Qed.

Theorem source_context_relativization_total M dom b c n :
  exists u v,source_context_relativization M dom b c n u v.
Proof.
  assert (HT:forall u v i,exists g,recursion_step M source_context_relativization_step
    (b .: c .: dom .: fun _=>zeroM M) u v i g).
  { intros u v i. destruct (beta_total M b c i) as [f HF].
    destruct (source_relativization_total M dom f) as [g HG].
    exists g. apply source_context_relativization_step_correct. exists f;auto. }
  assert (HP:forall u v u' v' i,prefix M u v u' v' i -> forall g,
    (recursion_step M source_context_relativization_step
      (b .: c .: dom .: fun _=>zeroM M) u v i g <->
     recursion_step M source_context_relativization_step
      (b .: c .: dom .: fun _=>zeroM M) u' v' i g)).
  { intros;rewrite !source_context_relativization_step_correct;reflexivity. }
  destruct (recursion_table_total M source_context_relativization_step
    (b .: c .: dom .: fun _=>zeroM M) HT HP n) as [u [v HUV]].
  exists u,v. intros i f g HI HF HG.
  pose proof (HUV i g HI HG) as HR.
  apply source_context_relativization_step_correct in HR as [f' [HF' HR]].
  assert (f=f') by (eapply beta_unique;eassumption). now subst f'.
Qed.

Theorem source_context_relativization_functional M dom b c n u v u' v' :
  source_context_relativization M dom b c n u v ->
  source_context_relativization M dom b c n u' v' ->
  forall i g g',coding_lt M i n -> beta M u v i g -> beta M u' v' i g' -> g=g'.
Proof.
  intros H H' i g g' HI HG HG'. destruct (beta_total M b c i) as [f HF].
  exact (source_relativization_functional M f dom g g'
    (H i f g HI HF HG) (H' i f g' HI HF HG')).
Qed.

Theorem source_context_relativization_member_forward M dom b c n u v f :
  source_context_relativization M dom b c n u v -> context_member M b c n f ->
  exists g,context_member M u v n g /\ source_relativization M dom f g.
Proof.
  intros H [i [HI HF]]. destruct (beta_total M u v i) as [g HG].
  exists g. split;[exists i;auto|exact (H i f g HI HF HG)].
Qed.

Theorem source_context_relativization_member_iff M dom b c n u v g :
  source_context_relativization M dom b c n u v ->
  (context_member M u v n g <->
    exists f,context_member M b c n f /\ source_relativization M dom f g).
Proof.
  intro H. split.
  - intros [i [HI HG]]. destruct (beta_total M b c i) as [f HF].
    exists f. split;[exists i;auto|exact (H i f g HI HF HG)].
  - intros [f [HF HR]].
    destruct (source_context_relativization_member_forward M dom b c n u v f H HF)
      as [g' [HG' HR']].
    assert (g'=g) by exact (source_relativization_functional M f dom g' g HR' HR).
    now subst g'.
Qed.

Theorem source_context_relativization_preserves_bound M dom b c n u v k :
  source_bounded M dom (succM M (zeroM M)) ->
  source_context_relativization M dom b c n u v -> context_bounded M b c n k ->
  context_bounded M u v n k.
Proof.
  intros HD HR HB g HG.
  apply (proj1 (source_context_relativization_member_iff M dom b c n u v g HR)) in HG.
  destruct HG as [f [HF HFG]].
  exact (source_relativization_preserves_bound M f dom k g HD (HB f HF) HFG).
Qed.

Theorem source_context_relativization_cons M dom b c n u v f g b' c' n' u' v' :
  source_context_relativization M dom b c n u v -> source_relativization M dom f g ->
  environment_cons M b c n f b' c' n' -> environment_cons M u v n g u' v' n' ->
  source_context_relativization M dom b' c' n' u' v'.
Proof.
  intros H HFG HS HT i x y HI HX HY. pose proof (proj1 HS) as EN.
  apply (proj2 (environment_lookup_inside M b' c' n' i x HI)) in HX.
  apply (proj2 (environment_lookup_inside M u' v' n' i y HI)) in HY.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[j E]];subst i.
  - apply (proj1 (environment_cons_head M b c n f b' c' n' x HS)) in HX.
    apply (proj1 (environment_cons_head M u v n g u' v' n' y HT)) in HY.
    now subst x y.
  - apply (proj1 (environment_cons_tail M b c n f b' c' n' j x HS)) in HX.
    apply (proj1 (environment_cons_tail M u v n g u' v' n' j y HT)) in HY.
    rewrite EN in HI. apply (proj1 (coding_lt_succ_cancel M j n)) in HI.
    apply (H j x y HI).
    + exact (proj1 (environment_lookup_inside M b c n j x HI) HX).
    + exact (proj1 (environment_lookup_inside M u v n j y HI) HY).
Qed.

Theorem source_context_relativization_formula_bound :
  bounded 6 (source_context_relativization_formula $0 $1 $2 $3 $4 $5).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Print Assumptions source_context_relativization_formula_correct.
Print Assumptions source_context_relativization_total.
Print Assumptions source_context_relativization_functional.
Print Assumptions source_context_relativization_member_iff.
Print Assumptions source_context_relativization_preserves_bound.
Print Assumptions source_context_relativization_cons.
