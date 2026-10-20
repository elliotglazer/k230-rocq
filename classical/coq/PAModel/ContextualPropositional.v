(** Finite propositional K programs applied within numerical contexts. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofTemplates TemplateCD TemplatePropositional QuantifierMacros
  ContextualProofs ContextualLogic QuotientAtomTemplates QuotationPayloads SetFormulaCodes NumericalVacuitySteps.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition contextual_inputs M b c n env Delta :=
  forall e, In e Delta -> forall v, code_relation M env e v -> contextually_provable M b c n v.

Theorem contextual_derivation_sound M b c n env G Delta e :
  template_guards_hold M env G -> contextual_inputs M b c n env Delta ->
  template_derivation G Delta e ->
  forall v, code_relation M env e v -> contextually_provable M b c n v.
Proof.
  intros HG HI HD. induction HD as [e He|e He|p q HDp IHp HDq IHq]; intros v Hv.
  - exact (HI e He v Hv).
  - apply contextual_global. exact (template_sound M env G e HG He v Hv).
  - destruct (code_relation_total M p env) as [a Ha].
    destruct (code_relation_total M (E_wim p q) env) as [h Hh].
    exact (contextual_mp_expression M b c n env p q a v h Ha Hv Hh (IHq a Ha) (IHp h Hh)).
Qed.

Corollary contextual_propositional_sound M b c n env Delta e :
  contextual_inputs M b c n env Delta -> template_derivation [] Delta e ->
  forall v, code_relation M env e v -> contextually_provable M b c n v.
Proof.
  apply contextual_derivation_sound. intros a d H. inversion H.
Qed.

Lemma contextual_inputs_one M b c n env e a : code_relation M env e a ->
  contextually_provable M b c n a -> contextual_inputs M b c n env [e].
Proof.
  intros He Ha f [<-|[]] v Hv.
  assert (v=a) by exact (code_relation_functional M e env v a Hv He). now subst v.
Qed.
Lemma contextual_inputs_two M b c n env e f a d :
  code_relation M env e a -> code_relation M env f d ->
  contextually_provable M b c n a -> contextually_provable M b c n d ->
  contextual_inputs M b c n env [e;f].
Proof.
  intros He Hf Ha Hd g [<-|[<-|[]]] v Hv.
  - assert (v=a) by exact (code_relation_functional M e env v a Hv He). now subst v.
  - assert (v=d) by exact (code_relation_functional M f env v d Hv Hf). now subst v.
Qed.

Lemma template_or_left G p q : template_proof G (E_wim p (E_or p q)).
Proof.
  unfold E_or,E_wn. apply template_discharge. do 2 apply template_deduction.
  apply (dmp G _ (CEconst 1)); [apply dthm,template_F|].
  apply (dmp G _ p); apply dhyp; cbn; tauto.
Qed.
Lemma template_or_right G p q : template_proof G (E_wim q (E_or p q)).
Proof. unfold E_or. apply template_K. Qed.
Lemma template_or_elimination G p q z : template_proof G
  (E_wim (E_wim p z) (E_wim (E_wim q z) (E_wim (E_or p q) z))).
Proof.
  apply template_discharge. do 3 apply template_deduction.
  apply (dmp G _ (E_wn (E_wn z))); [apply dthm,template_DNE|].
  apply template_deduction. unfold E_wn at 1.
  apply (dmp G _ z); [apply dhyp;cbn;tauto|].
  apply (dmp G _ q); [apply dhyp;cbn;tauto|].
  apply (dmp G _ (E_wn p)); [apply dhyp;cbn;tauto|].
  apply (dmp G _ (E_wn z)); [|apply dhyp;cbn;tauto].
  apply (dmp G _ (E_wim p z)); [apply dthm,template_contraposition|apply dhyp;cbn;tauto].
Qed.

Theorem contextual_conjunction_intro M b c n a d g :
  contextually_provable M b c n a -> contextually_provable M b c n d ->
  quotation_binary M SFAnd a d g -> contextually_provable M b c n g.
Proof.
  intros Ha Hd Hg. set (env := arguments2 a d (zeroM M)).
  apply (contextual_propositional_sound M b c n env [CEvar 0;CEvar 1]
    (E_wa (CEvar 0) (CEvar 1))).
  - exact (contextual_inputs_two M b c n env (CEvar 0) (CEvar 1) a d eq_refl eq_refl Ha Hd).
  - apply template_der_andi; apply dhyp;cbn;tauto.
  - exact Hg.
Qed.
Theorem contextual_conjunction_left M b c n a d g :
  quotation_binary M SFAnd a d g -> contextually_provable M b c n g ->
  contextually_provable M b c n a.
Proof.
  intros Hg Hproof. set (env := arguments2 a d (zeroM M)).
  apply (contextual_propositional_sound M b c n env [E_wa (CEvar 0) (CEvar 1)] (CEvar 0)).
  - exact (contextual_inputs_one M b c n env _ g Hg Hproof).
  - apply (template_der_andl [] _ (CEvar 0) (CEvar 1)),dhyp. cbn;auto.
  - reflexivity.
Qed.
Theorem contextual_conjunction_right M b c n a d g :
  quotation_binary M SFAnd a d g -> contextually_provable M b c n g ->
  contextually_provable M b c n d.
Proof.
  intros Hg Hproof. set (env := arguments2 a d (zeroM M)).
  apply (contextual_propositional_sound M b c n env [E_wa (CEvar 0) (CEvar 1)] (CEvar 1)).
  - exact (contextual_inputs_one M b c n env _ g Hg Hproof).
  - apply (template_der_andr [] _ (CEvar 0) (CEvar 1)),dhyp. cbn;auto.
  - reflexivity.
Qed.

Theorem contextual_disjunction_left M b c n a d g :
  quotation_binary M SFOr a d g -> contextually_provable M b c n a ->
  contextually_provable M b c n g.
Proof.
  intros Hg Hproof. set (env := arguments2 a d (zeroM M)).
  destruct (code_relation_total M (E_wim (CEvar 0) (E_or (CEvar 0) (CEvar 1))) env) as [s Hs].
  apply (contextual_mp_expression M b c n env (CEvar 0) (E_or (CEvar 0) (CEvar 1))
    a g s eq_refl Hg Hs Hproof).
  eapply contextual_template; [apply template_or_left|exact Hs].
Qed.
Theorem contextual_disjunction_right M b c n a d g :
  quotation_binary M SFOr a d g -> contextually_provable M b c n d ->
  contextually_provable M b c n g.
Proof.
  intros Hg Hproof. set (env := arguments2 a d (zeroM M)).
  destruct (code_relation_total M (E_wim (CEvar 1) (E_or (CEvar 0) (CEvar 1))) env) as [s Hs].
  apply (contextual_mp_expression M b c n env (CEvar 1) (E_or (CEvar 0) (CEvar 1))
    d g s eq_refl Hg Hs Hproof).
  eapply contextual_template; [apply template_or_right|exact Hs].
Qed.

Theorem contextual_disjunction_elimination M b c n a d z disj az dz :
  quotation_binary M SFOr a d disj -> implication_graph M a z az ->
  implication_graph M d z dz -> contextually_provable M b c n disj ->
  contextually_provable M b c n az -> contextually_provable M b c n dz ->
  contextually_provable M b c n z.
Proof.
  intros Hdisj Haz Hdz Hp Hazp Hdzp.
  set (env := code_parameters a d z (zeroM M)).
  assert (Edisj : code_relation M env (E_or (CEvar 0) (CEvar 1)) disj) by exact Hdisj.
  pose proof (proj2 (expression_implication_iff M env (CEvar 0) (CEvar 2)
    a z az eq_refl eq_refl) Haz) as Eaz.
  pose proof (proj2 (expression_implication_iff M env (CEvar 1) (CEvar 2)
    d z dz eq_refl eq_refl) Hdz) as Edz.
  destruct (code_relation_total M (E_wim (E_or (CEvar 0) (CEvar 1)) (CEvar 2)) env)
    as [third E3].
  destruct (code_relation_total M (E_wim (E_wim (CEvar 1) (CEvar 2))
    (E_wim (E_or (CEvar 0) (CEvar 1)) (CEvar 2))) env) as [second E2].
  destruct (code_relation_total M (E_wim (E_wim (CEvar 0) (CEvar 2))
    (E_wim (E_wim (CEvar 1) (CEvar 2))
      (E_wim (E_or (CEvar 0) (CEvar 1)) (CEvar 2)))) env) as [first E1].
  assert (H2 : contextually_provable M b c n second).
  { eapply contextual_mp_expression; [exact Eaz|exact E2|exact E1|exact Hazp|].
    eapply contextual_template; [apply template_or_elimination|exact E1]. }
  assert (H3 : contextually_provable M b c n third).
  { exact (contextual_mp_expression M b c n env _ _ dz third second Edz E3 E2 Hdzp H2). }
  exact (contextual_mp_expression M b c n env _ (CEvar 2) disj z third Edisj eq_refl E3 Hp H3).
Qed.

Theorem contextual_explosion M b c n f :
  contextually_provable M b c n (code_numeral M 1) -> contextually_provable M b c n f.
Proof.
  intro Hfalse. set (env := fun _ : nat => f).
  destruct (code_relation_total M (E_wim (CEconst 1) (CEvar 0)) env) as [h Hh].
  apply (contextual_mp_expression M b c n env (CEconst 1) (CEvar 0)
    (code_numeral M 1) f h eq_refl eq_refl Hh Hfalse).
  eapply contextual_template; [apply template_F|exact Hh].
Qed.

Theorem contextual_peirce M b c n a d x y f :
  implication_graph M a d x -> implication_graph M x a y ->
  implication_graph M y a f -> contextually_provable M b c n f.
Proof.
  intros Hx Hy Hf. set (env := arguments2 a d (zeroM M)).
  pose proof (proj2 (expression_implication_iff M env (CEvar 0) (CEvar 1)
    a d x eq_refl eq_refl) Hx) as Ex.
  pose proof (proj2 (expression_implication_iff M env (E_wim (CEvar 0) (CEvar 1)) (CEvar 0)
    x a y Ex eq_refl) Hy) as Ey.
  pose proof (proj2 (expression_implication_iff M env
    (E_wim (E_wim (CEvar 0) (CEvar 1)) (CEvar 0)) (CEvar 0) y a f Ey eq_refl) Hf) as Ef.
  eapply contextual_template; [apply template_P|exact Ef].
Qed.

Print Assumptions contextual_derivation_sound.
Print Assumptions template_or_elimination.
Print Assumptions contextual_conjunction_intro.
Print Assumptions contextual_conjunction_left.
Print Assumptions contextual_disjunction_left.
Print Assumptions contextual_disjunction_right.
Print Assumptions contextual_disjunction_elimination.
Print Assumptions contextual_explosion.
Print Assumptions contextual_peirce.



