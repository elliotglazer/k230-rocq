(** Alpha conversion for host-finite formulas with an explicit finite tree
    of model-valued binder names. No choice function over internal syntax is
    used: the plan is ordinary finite data, and hygiene is stated recursively. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT Pairing
  CodeExpressions CodeDescent CodeTags NumericalProofs ProofTemplates
  NamedLeibnizSteps NamedAlpha NamedExistential NamedSubstitution NamedSubstitutionRules
  NamedBinderFresh NamedBinderConstructors FreshNames NumericalEquivalence
  FiniteTemplateEvaluation FiniteTemplateRebase TemplateExistsAlpha
  TemplateNamedSubstitution TemplateBinderFresh QuotientAtomTemplates
  QuotationPayloads SetFormulaCodes.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.

Inductive finite_binder_plan (M : Model) : Type :=
| PlanLeaf : finite_binder_plan M
| PlanBinary : finite_binder_plan M -> finite_binder_plan M -> finite_binder_plan M
| PlanBind : carrier M -> finite_binder_plan M -> finite_binder_plan M.
Arguments PlanLeaf {M}.
Arguments PlanBinary {M} _ _.
Arguments PlanBind {M} _ _.

Fixpoint plan_avoids M (p : finite_binder_plan M) y : Prop :=
  match p with
  | PlanLeaf => True
  | PlanBinary a b => plan_avoids M a y /\ plan_avoids M b y
  | PlanBind x a => x<>y /\ plan_avoids M a y
  end.
Fixpoint plan_proper M (p : finite_binder_plan M) : Prop :=
  match p with
  | PlanLeaf => True
  | PlanBinary a b => plan_proper M a /\ plan_proper M b
  | PlanBind x a => x<>zeroM M /\ plan_avoids M a x /\ plan_proper M a
  end.
Definition plan_hygienic M (eta : nat -> carrier M) p :=
  plan_proper M p /\ forall i,plan_avoids M p (eta i).

Fixpoint named_plan_evaluation M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff)
  (eta : nat -> carrier M) (p : finite_binder_plan M) f : Prop :=
  match phi,p with
  | falsity,PlanLeaf => f=code_numeral M 1
  | atom P args,PlanLeaf =>
      tagged_pair_graph M (match P with elem=>1|equal=>3 end)
        (eta (sf_index (Vector.hd args)))
        (eta (sf_index (Vector.hd (Vector.tl args)))) f
  | bin op a b,PlanBinary pa pb => exists x y,
      named_plan_evaluation M a eta pa x /\ named_plan_evaluation M b eta pb y /\
      quotation_binary M (template_binary_head op) x y f
  | quant q a,PlanBind x pa => exists v,
      named_plan_evaluation M a (x .: eta) pa v /\
      template_quantified M (match q with All=>true|Ex=>false end) x v f
  | _,_ => False
  end.

Lemma plan_hygienic_left M eta a b :
  plan_hygienic M eta (PlanBinary a b) -> plan_hygienic M eta a.
Proof. intros [[HA HB] HE]. split;[exact HA|intro i;exact (proj1 (HE i))]. Qed.
Lemma plan_hygienic_right M eta a b :
  plan_hygienic M eta (PlanBinary a b) -> plan_hygienic M eta b.
Proof. intros [[HA HB] HE]. split;[exact HB|intro i;exact (proj2 (HE i))]. Qed.
Lemma plan_hygienic_common_child M eta x p y :
  plan_hygienic M eta (PlanBind x p) -> plan_avoids M p y ->
  plan_hygienic M (y .: eta) p.
Proof.
  intros [[Hx [HA HP]] HE] HY. split;[exact HP|].
  intros [|i];[exact HY|exact (proj2 (HE i))].
Qed.

Lemma plan_binary_substitution M op a b f a' b' g x y :
  x<>zeroM M ->
  quotation_binary M (template_binary_head op) a b f ->
  quotation_binary M (template_binary_head op) a' b' g ->
  named_substitution M a x y a' -> named_substitution M b x y b' ->
  named_substitution M f x y g.
Proof.
  intros Hx HF HG HA HB.
  set (rho:=a .: b .: fun _=>zeroM M).
  set (sigma:=a' .: b' .: fun _=>zeroM M).
  assert (EA : expression_named_substitution M rho sigma x y (CEvar 0) (CEvar 0)).
  { intros u v -> ->. exact HA. }
  assert (EB : expression_named_substitution M rho sigma x y (CEvar 1) (CEvar 1)).
  { intros u v -> ->. exact HB. }
  destruct op;cbn [template_binary_head quotation_binary quotation_binary_expression] in HF,HG.
  - exact (expression_ns_conjunction M rho sigma x y (CEvar 0) (CEvar 1)
      (CEvar 0) (CEvar 1) Hx EA EB f g HF HG).
  - exact (expression_ns_disjunction M rho sigma x y (CEvar 0) (CEvar 1)
      (CEvar 0) (CEvar 1) Hx EA EB f g HF HG).
  - exact (expression_ns_implication M rho sigma x y (CEvar 0) (CEvar 1)
      (CEvar 0) (CEvar 1) EA EB f g HF HG).
Qed.

Lemma plan_quantified_substitution M universal z a f a' g x y :
  x<>zeroM M -> z<>x -> z<>y ->
  template_quantified M universal z a f -> template_quantified M universal z a' g ->
  named_substitution M a x y a' -> named_substitution M f x y g.
Proof.
  intros Hx Hzx Hzy HF HG HA.
  set (rho:=z .: a .: fun _=>zeroM M).
  set (sigma:=z .: a' .: fun _=>zeroM M).
  assert (EA : expression_named_substitution M rho sigma x y (CEvar 1) (CEvar 1)).
  { intros u v -> ->. exact HA. }
  destruct universal.
  - eapply (expression_ns_universal M rho sigma x y (CEvar 0) (CEvar 0)
      (CEvar 1) (CEvar 1) z eq_refl eq_refl Hzx Hzy EA f g).
    + exact (proj2 (template_quantified_graph M rho true (CEvar 0) (CEvar 1) z a f eq_refl eq_refl) HF).
    + exact (proj2 (template_quantified_graph M sigma true (CEvar 0) (CEvar 1) z a' g eq_refl eq_refl) HG).
  - eapply (expression_ns_existential M rho sigma x y (CEvar 0) (CEvar 0)
      (CEvar 1) (CEvar 1) z Hx eq_refl eq_refl Hzx Hzy EA f g).
    + exact (proj2 (template_quantified_graph M rho false (CEvar 0) (CEvar 1) z a f eq_refl eq_refl) HF).
    + exact (proj2 (template_quantified_graph M sigma false (CEvar 0) (CEvar 1) z a' g eq_refl eq_refl) HG).
Qed.

Theorem named_plan_substitution M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall p eta eta' x y f g,
    x<>zeroM M -> plan_avoids M p x -> plan_avoids M p y ->
    (forall i,named_replace M x y (eta i) (eta' i)) ->
    named_plan_evaluation M phi eta p f -> named_plan_evaluation M phi eta' p g ->
    named_substitution M f x y g.
Proof.
  induction phi as [|fl P ts|fl op a IHa b IHb|fl q a IH];
    intros p eta eta' x y f g Hx HX HY HE HF HG;
    destruct p as [|pa pb|z pa];cbn [named_plan_evaluation] in HF,HG;try contradiction.
  - subst f g. now apply named_substitution_one_fixed.
  - destruct P.
    + eapply (ns_combine_atom M false);[exact HF|exact HG|apply HE|apply HE].
    + eapply (ns_combine_atom M true);[exact HF|exact HG|apply HE|apply HE].
  - destruct HX as [HXA HXB],HY as [HYA HYB].
    destruct HF as [u [v [HU [HV HF]]]],HG as [u' [v' [HU' [HV' HG]]]].
    eapply plan_binary_substitution;[exact Hx|exact HF|exact HG| |].
    + exact (IHa pa eta eta' x y u u' Hx HXA HYA HE HU HU').
    + exact (IHb pb eta eta' x y v v' Hx HXB HYB HE HV HV').
  - destruct HX as [Hzx HX],HY as [Hzy HY].
    destruct HF as [u [HU HF]],HG as [v [HV HG]].
    eapply plan_quantified_substitution;[exact Hx|exact Hzx|exact Hzy|exact HF|exact HG|].
    apply (IH pa (z .: eta) (z .: eta') x y u v Hx HX HY);try assumption.
    intros [|i];[right;auto|apply HE].
Qed.

Lemma plan_binary_binder_absent M op a b f y :
  quotation_binary M (template_binary_head op) a b f ->
  named_binder_absent M a y -> named_binder_absent M b y -> named_binder_absent M f y.
Proof.
  intros HF HA HB. set (rho:=a .: b .: fun _=>zeroM M).
  assert (EA : expression_binder_absent M rho y (CEvar 0)).
  { intros u ->. exact HA. }
  assert (EB : expression_binder_absent M rho y (CEvar 1)).
  { intros u ->. exact HB. }
  destruct op;cbn [template_binary_head quotation_binary quotation_binary_expression] in HF.
  - exact (expression_binder_absent_conjunction M rho y (CEvar 0) (CEvar 1) EA EB f HF).
  - exact (expression_binder_absent_disjunction M rho y (CEvar 0) (CEvar 1) EA EB f HF).
  - exact (expression_binder_absent_implication M rho y (CEvar 0) (CEvar 1) EA EB f HF).
Qed.
Lemma plan_quantified_binder_absent M universal x a f y :
  x<>y -> template_quantified M universal x a f ->
  named_binder_absent M a y -> named_binder_absent M f y.
Proof.
  intros Hxy HF HA. set (rho:=x .: a .: fun _=>zeroM M).
  assert (EX : forall z,code_relation M rho (CEvar 0) z -> z<>y).
  { intros z ->. exact Hxy. }
  assert (EA : expression_binder_absent M rho y (CEvar 1)).
  { intros u ->. exact HA. }
  destruct universal.
  - apply (expression_binder_absent_universal M rho y (CEvar 0) (CEvar 1) EX EA f).
    exact (proj2 (template_quantified_graph M rho true (CEvar 0) (CEvar 1) x a f eq_refl eq_refl) HF).
  - apply (expression_binder_absent_existential M rho y (CEvar 0) (CEvar 1) EX EA f).
    exact (proj2 (template_quantified_graph M rho false (CEvar 0) (CEvar 1) x a f eq_refl eq_refl) HF).
Qed.

Theorem named_plan_binder_absent M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall p eta y f,plan_avoids M p y -> named_plan_evaluation M phi eta p f ->
    named_binder_absent M f y.
Proof.
  induction phi as [|fl P ts|fl op a IHa b IHb|fl q a IH];
    intros p eta y f HY HF;destruct p as [|pa pb|x pa];
    cbn [named_plan_evaluation] in HF;try contradiction.
  - subst f. apply named_binder_absent_one.
  - destruct P.
    + eapply named_binder_absent_membership. exact HF.
    + eapply named_binder_absent_equality. exact HF.
  - destruct HY as [HYA HYB],HF as [u [v [HU [HV HF]]]].
    eapply plan_binary_binder_absent;[exact HF|exact (IHa pa eta y u HYA HU)|exact (IHb pb eta y v HYB HV)].
  - destruct HY as [Hxy HY],HF as [v [HV HF]].
    eapply plan_quantified_binder_absent;[exact Hxy|exact HF|exact (IH pa (x .: eta) y v HY HV)].
Qed.

Theorem named_plan_reenvironment_total M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall p eta f, named_plan_evaluation M phi eta p f ->
    forall eta',exists g,named_plan_evaluation M phi eta' p g.
Proof.
  induction phi as [|fl P ts|fl op a IHa b IHb|fl q a IH];
    intros p eta f HF eta';destruct p as [|pa pb|x pa];
    cbn [named_plan_evaluation] in HF;try contradiction.
  - exists (code_numeral M 1). reflexivity.
  - apply tagged_pair_total.
  - destruct HF as [u [v [HU [HV HF]]]].
    destruct (IHa pa eta u HU eta') as [u' HU'].
    destruct (IHb pb eta v HV eta') as [v' HV'].
    destruct (quotation_binary_total M (template_binary_head op) u' v') as [g HG].
    exists g,u',v'. auto.
  - destruct HF as [u [HU HF]].
    destruct (IH pa (x .: eta) u HU (x .: eta')) as [v HV].
    destruct (template_quantified_total M (match q with All=>true|Ex=>false end) x v) as [g HG].
    exists g,v. auto.
Qed.

Fixpoint plan_sum M (p : finite_binder_plan M) : carrier M :=
  match p with PlanLeaf=>zeroM M|PlanBinary a b=>addM M (plan_sum M a) (plan_sum M b)
  |PlanBind x a=>addM M x (plan_sum M a) end.
Fixpoint plan_below M (p : finite_binder_plan M) y : Prop :=
  match p with PlanLeaf=>True|PlanBinary a b=>plan_below M a y /\ plan_below M b y
  |PlanBind x a=>coding_lt M x y /\ plan_below M a y end.
Lemma plan_below_avoids M p y : plan_below M p y -> plan_avoids M p y.
Proof.
  induction p;cbn;auto.
  - intros [HA HB]. auto.
  - intros [Hx HA]. split;[exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) _ _ Hx)|auto].
Qed.
Section PlanBound.
Variable M : Model.
Add Ring named_plan_ring : (model_semiring M).
Lemma plan_below_sum p : forall c,plan_below M p (succM M (addM M c (plan_sum M p))).
Proof.
  induction p as [|a IHa b IHb|x a IH];intro c;cbn [plan_below plan_sum];[exact I| |].
  - split.
    + replace (addM M c (addM M (plan_sum M a) (plan_sum M b)))
        with (addM M (addM M c (plan_sum M b)) (plan_sum M a)) by ring. apply IHa.
    + replace (addM M c (addM M (plan_sum M a) (plan_sum M b)))
        with (addM M (addM M c (plan_sum M a)) (plan_sum M b)) by ring. apply IHb.
  - split.
    + exists (addM M c (plan_sum M a)). f_equal. ring.
    + replace (addM M c (addM M x (plan_sum M a)))
        with (addM M (addM M c x) (plan_sum M a)) by ring. apply IH.
Qed.
Lemma plan_common_fresh p q a b x z :
  exists y,coding_lt M a y /\ coding_lt M b y /\ coding_lt M x y /\ coding_lt M z y /\
    plan_avoids M p y /\ plan_avoids M q y.
Proof.
  set (s:=addM M (addM M a b) (addM M x z)).
  set (y:=succM M (addM M s (addM M (plan_sum M p) (plan_sum M q)))).
  exists y. split.
  - exists (addM M b (addM M (addM M x z) (addM M (plan_sum M p) (plan_sum M q)))).
    unfold y,s. f_equal. ring.
  - split.
    + exists (addM M a (addM M (addM M x z) (addM M (plan_sum M p) (plan_sum M q)))).
      unfold y,s. f_equal. ring.
    + split.
      * exists (addM M (addM M a b) (addM M z (addM M (plan_sum M p) (plan_sum M q)))).
        unfold y,s. f_equal. ring.
      * split.
        -- exists (addM M (addM M a b) (addM M x (addM M (plan_sum M p) (plan_sum M q)))).
           unfold y,s. f_equal. ring.
        -- split;apply plan_below_avoids;unfold y.
           ++ replace (addM M s (addM M (plan_sum M p) (plan_sum M q)))
                with (addM M (addM M s (plan_sum M q)) (plan_sum M p)) by ring.
              apply plan_below_sum.
           ++ replace (addM M s (addM M (plan_sum M p) (plan_sum M q)))
                with (addM M (addM M s (plan_sum M p)) (plan_sum M q)) by ring.
              apply plan_below_sum.
Qed.
End PlanBound.

Lemma named_plan_outer_alpha M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff)
  p eta x y a v f g universal :
  x<>zeroM M -> y<>zeroM M -> x<>y -> (forall i,eta i<>x) ->
  plan_avoids M p x -> plan_avoids M p y -> coding_lt M a y ->
  named_plan_evaluation M phi (x .: eta) p a ->
  named_plan_evaluation M phi (y .: eta) p v ->
  template_quantified M universal x a f -> template_quantified M universal y v g ->
  numerical_equivalent M f g.
Proof.
  intros Hx Hy Hxy HE HPX HPY Hay HA HV HF HG.
  assert (HR : forall i,named_replace M x y ((x .: eta) i) ((y .: eta) i)).
  { intros [|i];cbn;[left;split;reflexivity|right;split;[apply HE|reflexivity]]. }
  pose proof (named_plan_substitution M phi p (x .: eta) (y .: eta) x y a v
    Hx HPX HPY HR HA HV) as HS.
  pose proof (named_plan_binder_absent M phi p (x .: eta) x a HPX HA) as HB.
  pose proof (formula_above_is_fresh M a y Hay) as HY.
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (f .: g .: fun _=>zeroM M)) as [forward Hforward].
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (g .: f .: fun _=>zeroM M)) as [backward Hbackward].
  destruct universal.
  - destruct (numerical_named_alpha M a x y v f g forward backward
      Hxy HB HY HS HF HG Hforward Hbackward) as [PF PB].
    exact (numerical_equivalent_of_proofs M f g forward backward Hforward Hbackward PF PB).
  - destruct (numerical_named_exists_alpha M a x y v f g forward backward
      Hx Hy Hxy HB HY HS HF HG Hforward Hbackward) as [PF PB].
    exact (numerical_equivalent_of_proofs M f g forward backward Hforward Hbackward PF PB).
Qed.

Theorem finite_named_plan_alpha M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall eta p q f g,
    plan_hygienic M eta p -> plan_hygienic M eta q ->
    named_plan_evaluation M phi eta p f -> named_plan_evaluation M phi eta q g ->
    numerical_equivalent M f g.
Proof.
  induction phi as [|fl P ts|fl op a IHa b IHb|fl quant a IH];
    intros eta p q f g HP HQ HF HG;
    destruct p as [|pa pb|x pa],q as [|qa qb|z qa];
    cbn [named_plan_evaluation] in HF,HG;try contradiction.
  - subst f g. apply numerical_equivalent_refl.
  - assert (f=g) by (eapply tagged_pair_functional;eassumption). subst g.
    apply numerical_equivalent_refl.
  - destruct HF as [u [v [HU [HV HF]]]],HG as [u' [v' [HU' [HV' HG]]]].
    apply (numerical_equivalent_binary M (template_binary_head op) u v u' v' f g);try assumption.
    + apply (IHa eta pa qa u u');try assumption.
      * exact (plan_hygienic_left M eta pa pb HP).
      * exact (plan_hygienic_left M eta qa qb HQ).
    + apply (IHb eta pb qb v v');try assumption.
      * exact (plan_hygienic_right M eta pa pb HP).
      * exact (plan_hygienic_right M eta qa qb HQ).
  - destruct HF as [u [HU HF]],HG as [v [HV HG]].
    destruct (plan_common_fresh M pa qa u v x z)
      as [y [Huy [Hvy [Hxy [Hzy [HPY HQY]]]]]].
    destruct (named_plan_reenvironment_total M a pa (x .: eta) u HU (y .: eta)) as [u' HU'].
    destruct (named_plan_reenvironment_total M a qa (z .: eta) v HV (y .: eta)) as [v' HV'].
    destruct (template_quantified_total M (match quant with All=>true|Ex=>false end) y u') as [f' HF'].
    destruct (template_quantified_total M (match quant with All=>true|Ex=>false end) y v') as [g' HG'].
    assert (Hy0 : y<>zeroM M).
    { intro E. subst y. exact (coding_not_lt_zero M u Huy). }
    assert (Hxy' : x<>y) by exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) _ _ Hxy).
    assert (Hzy' : z<>y) by exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) _ _ Hzy).
    eapply (numerical_equivalent_trans M f f' g).
    + apply (named_plan_outer_alpha M a pa eta x y u u' f f'
        (match quant with All=>true|Ex=>false end));try assumption.
      * exact (proj1 (proj1 HP)).
      * intros i E. apply (proj1 (proj2 HP i)). symmetry. exact E.
      * exact (proj1 (proj2 (proj1 HP))).
    + eapply (numerical_equivalent_trans M f' g' g).
      * apply (template_quantified_equivalent M (match quant with All=>true|Ex=>false end) y u' v' f' g');try assumption.
        apply (IH (y .: eta) pa qa u' v');try assumption.
        -- exact (plan_hygienic_common_child M eta x pa y HP HPY).
        -- exact (plan_hygienic_common_child M eta z qa y HQ HQY).
      * apply numerical_equivalent_sym.
        apply (named_plan_outer_alpha M a qa eta z y v v' g g'
          (match quant with All=>true|Ex=>false end));try assumption.
        -- exact (proj1 (proj1 HQ)).
        -- intros i E. apply (proj1 (proj2 HQ i)). symmetry. exact E.
        -- exact (proj1 (proj2 (proj1 HQ))).
Qed.

Print Assumptions named_plan_substitution.
Print Assumptions named_plan_binder_absent.
Print Assumptions named_plan_reenvironment_total.
Print Assumptions plan_common_fresh.
Print Assumptions finite_named_plan_alpha.
