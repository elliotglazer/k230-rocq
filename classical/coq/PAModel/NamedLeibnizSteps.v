(** Finite K proof operations for named Leibniz transport.  These operations
    build numerical Hilbert proofs; no formula completeness rule is used. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions CodeDescent CodeTags
  NumericalProofs ProofClosure ProofTemplates TemplateCD TemplatePropositional
  ProofMacros QuantifierMacros EqualityMacros NumericalEquality
  NumericalVacuitySteps NumericalVacuity NamedSubstitutionRules.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Import List.ListNotations.
Open Scope list_scope.
Unset Implicit Arguments.

Definition ns_proof M env e :=
  forall f, code_relation M env e f -> numerically_provable M f.

Definition ns_under M h a b := forall p q,
  implication_graph M a b p -> implication_graph M h p q ->
  numerically_provable M q.

Definition ns_under_formula (h a b : term) : form :=
  ∀∀ (implication_formula (code_lift2 a) (code_lift2 b) $1 →
    implication_formula (code_lift2 h) $1 $0 → numerically_provable_formula $0).

Local Opaque holds implication_formula numerically_provable_formula.

Lemma ns_under_formula_correct M rho h a b :
  holds M rho (ns_under_formula h a b) <->
  ns_under M (evalM M rho h) (evalM M rho a) (evalM M rho b).
Proof.
  unfold ns_under_formula,ns_under. repeat setoid_rewrite holds_all.
  repeat setoid_rewrite holds_imp. setoid_rewrite implication_formula_correct.
  setoid_rewrite numerically_provable_formula_correct.
  setoid_rewrite code_eval_lift2. reflexivity.
Qed.

Lemma ns_under_expression M env H A B h a b :
  code_relation M env H h -> code_relation M env A a -> code_relation M env B b ->
  (ns_proof M env (E_wim H (E_wim A B)) <-> ns_under M h a b).
Proof.
  intros HH HA HB. split.
  - intros HP p q Hp Hq. apply HP.
    exact (proj2 (expression_implication_iff M env H (E_wim A B) h p q HH
      (proj2 (expression_implication_iff M env A B a b p HA HB) Hp)) Hq).
  - intros HP q Hq. destruct (code_relation_total M (E_wim A B) env) as [p Hp].
    apply (HP p q).
    + exact (expression_implication_graph M env A B a b p HA HB Hp).
    + exact (expression_implication_graph M env H (E_wim A B) h p q HH Hp Hq).
Qed.

Lemma ns_proof_template M env e : template_proof nil e -> ns_proof M env e.
Proof. exact (unguarded_template_sound M env e). Qed.
Lemma ns_proof_mp M env a b : ns_proof M env a -> ns_proof M env (E_wim a b) -> ns_proof M env b.
Proof.
  intros HA HI f Hf. destruct (code_relation_total M a env) as [u Hu].
  destruct (code_relation_total M (E_wim a b) env) as [v Hv].
  exact (numerical_mp M u f v (HA u Hu) (HI v Hv)
    (expression_implication_graph M env a b u f v Hu Hf Hv)).
Qed.
Lemma ns_proof_macro M env inputs e :
  (forall p,In p inputs -> ns_proof M env p) -> proof_macro nil inputs e -> ns_proof M env e.
Proof. intros H HM. exact (unguarded_macro_sound M env inputs e H HM). Qed.
Lemma ns_proof_weaken M env h p : ns_proof M env p -> ns_proof M env (E_wim h p).
Proof.
  intro HP. eapply ns_proof_mp;[exact HP|]. apply ns_proof_template,template_K.
Qed.
Lemma ns_under_refl M h f : ns_under M h f f.
Proof.
  apply (proj1 (ns_under_expression M (h .: f .: fun _ => zeroM M)
    (CEvar 0) (CEvar 1) (CEvar 1) h f f eq_refl eq_refl eq_refl)).
  apply ns_proof_weaken,ns_proof_template,template_I.
Qed.

Lemma ns_macro_binary h a a' b b' :
  proof_macro nil (E_wim h (E_wim a' a) :: E_wim h (E_wim b b') :: nil)
    (E_wim h (E_wim (E_wim a b) (E_wim a' b'))).
Proof.
  apply macro_discharge,macro_deduction,macro_deduction,macro_deduction.
  eapply md_mp with (a:=b).
  - eapply md_mp with (a:=a).
    + eapply md_mp with (a:=a').
      * apply md_hyp;cbn;auto.
      * eapply md_mp with (a:=h);[apply md_hyp;cbn;auto|].
        apply md_global,PM_input;cbn;auto.
    + apply md_hyp;cbn;auto.
  - eapply md_mp with (a:=h);[apply md_hyp;cbn;auto|].
    apply md_global,PM_input;cbn;auto.
Qed.

Lemma ns_under_binary M h a a' b b' f g :
  ns_under M h a' a -> ns_under M h b b' ->
  implication_graph M a b f -> implication_graph M a' b' g -> ns_under M h f g.
Proof.
  intros HA HB Hf Hg. set (env := h .: a .: a' .: b .: b' .: fun _ => zeroM M).
  assert (Ef : code_relation M env (E_wim (CEvar 1) (CEvar 3)) f).
  { exact (proj2 (expression_implication_iff M env (CEvar 1) (CEvar 3) a b f eq_refl eq_refl) Hf). }
  assert (Eg : code_relation M env (E_wim (CEvar 2) (CEvar 4)) g).
  { exact (proj2 (expression_implication_iff M env (CEvar 2) (CEvar 4) a' b' g eq_refl eq_refl) Hg). }
  apply (proj1 (ns_under_expression M env (CEvar 0) (E_wim (CEvar 1) (CEvar 3))
    (E_wim (CEvar 2) (CEvar 4)) h f g eq_refl Ef Eg)).
  apply (ns_proof_macro M env (E_wim (CEvar 0) (E_wim (CEvar 2) (CEvar 1)) ::
    E_wim (CEvar 0) (E_wim (CEvar 3) (CEvar 4)) :: nil)).
  - intros p [<-|[<-|[]]].
    + exact (proj2 (ns_under_expression M env (CEvar 0) (CEvar 2) (CEvar 1) h a' a eq_refl eq_refl eq_refl) HA).
    + exact (proj2 (ns_under_expression M env (CEvar 0) (CEvar 3) (CEvar 4) h b b' eq_refl eq_refl eq_refl) HB).
  - apply ns_macro_binary.
Qed.

Lemma ns_macro_all z h a b :
  proof_macro nil (E_wim h (E_wim a b) :: E_vac z h :: nil)
    (E_wim h (E_wim (E_wal z a) (E_wal z b))).
Proof.
  eapply macro_syl with (q:=E_wal z (E_wim a b)).
  - eapply macro_syl with (q:=E_wal z h).
    + apply PM_input;cbn;auto.
    + apply macro_all_monotone,PM_input;cbn;auto.
  - apply PM_template,template_r2.
Qed.

Lemma ns_under_all M x y h z a b f g :
  equality_graph M x y h -> z<>x -> z<>y -> ns_under M h a b ->
  universal_graph M z a f -> universal_graph M z b g -> ns_under M h f g.
Proof.
  intros Hh Hzx Hzy HAB Hf Hg. set (env := z .: h .: a .: b .: fun _ => zeroM M).
  assert (Ef : code_relation M env (E_wal (CEvar 0) (CEvar 2)) f).
  { exact (proj2 (expression_universal_iff M env (CEvar 0) (CEvar 2) z a f eq_refl eq_refl) Hf). }
  assert (Eg : code_relation M env (E_wal (CEvar 0) (CEvar 3)) g).
  { exact (proj2 (expression_universal_iff M env (CEvar 0) (CEvar 3) z b g eq_refl eq_refl) Hg). }
  apply (proj1 (ns_under_expression M env (CEvar 1) (E_wal (CEvar 0) (CEvar 2))
    (E_wal (CEvar 0) (CEvar 3)) h f g eq_refl Ef Eg)).
  apply (ns_proof_macro M env (E_wim (CEvar 1) (E_wim (CEvar 2) (CEvar 3)) ::
    E_vac (CEvar 0) (CEvar 1) :: nil)).
  - intros p [<-|[<-|[]]].
    + exact (proj2 (ns_under_expression M env (CEvar 1) (CEvar 2) (CEvar 3) h a b eq_refl eq_refl eq_refl) HAB).
    + intros v Hv. apply (numerical_atom_vacuity M true x y h z v Hh Hzx Hzy).
      exact (proj1 (expression_vacuity_graph M env (CEvar 0) (CEvar 1) z h v eq_refl eq_refl) Hv).
  - apply ns_macro_all.
Qed.

Lemma ns_proof_reflexivity M env X : ns_proof M env (E_weq X X).
Proof.
  intros f Hf. destruct (code_relation_total M X env) as [x HX].
  exact (numerical_expression_reflexivity M env X x f HX Hf).
Qed.
Lemma ns_proof_symmetry M env X Y : ns_proof M env (E_wim (E_weq X Y) (E_weq Y X)).
Proof.
  apply (ns_proof_macro M env (E_weq X X :: nil)).
  - intros p [<-|[]]. apply ns_proof_reflexivity.
  - apply macro_eq_sym,PM_input;cbn;auto.
Qed.

Lemma ns_proof_atom_transport M env eq A A' B B' :
  ns_proof M env (E_wim (E_weq A A') (E_wim (E_weq B B')
    (E_wim (E_atom eq A B) (E_atom eq A' B')))).
Proof.
  destruct eq;cbn [E_atom].
  - apply (ns_proof_macro M env (E_weq A' A' :: nil)).
    + intros p [<-|[]]. apply ns_proof_reflexivity.
    + apply macro_eq_transport,PM_input;cbn;auto.
  - apply (ns_proof_macro M env nil).
    + intros p [].
    + apply macro_member_transport.
Qed.

Lemma ns_macro_atom h r s f g :
  proof_macro nil (E_wim h r :: E_wim h s :: E_wim r (E_wim s (E_wim f g)) :: nil)
    (E_wim h (E_wim f g)).
Proof.
  apply macro_discharge,macro_deduction,macro_deduction.
  eapply md_mp with (a:=f);[apply md_hyp;cbn;auto|].
  eapply md_mp with (a:=s).
  - eapply md_mp with (a:=h);[apply md_hyp;cbn;auto|].
    apply md_global,PM_input;cbn;auto.
  - eapply md_mp with (a:=r).
    + eapply md_mp with (a:=h);[apply md_hyp;cbn;auto|].
      apply md_global,PM_input;cbn;auto.
    + apply md_global,PM_input;cbn;auto.
Qed.

Lemma ns_replace_coordinate M env X Y A A' x y a a' :
  code_relation M env X x -> code_relation M env Y y ->
  code_relation M env A a -> code_relation M env A' a' ->
  named_replace M x y a a' ->
  ns_proof M env (E_wim (E_weq X Y) (E_weq A A')) /\
  ns_proof M env (E_wim (E_weq X Y) (E_weq A' A)).
Proof.
  intros HX HY HA HA' Hrep.
  destruct Hrep as [[-> ->]|[Hne ->]].
  - split; intros f Hf.
    + apply (ns_proof_template M env (E_wim (E_weq X Y) (E_weq X Y)) (template_I nil _) f).
      destruct (code_relation_total M (E_weq X Y) env) as [h Hh].
      assert (Ha : code_relation M env (E_weq A A') h).
      { apply (proj2 (expression_equality_graph M env A A' x y h HA HA')).
        exact (proj1 (expression_equality_graph M env X Y x y h HX HY) Hh). }
      exact (proj2 (expression_implication_iff M env _ _ h h f Hh Hh)
        (proj1 (expression_implication_iff M env _ _ h h f Hh Ha) Hf)).
    + destruct (code_relation_total M (E_weq X Y) env) as [h Hh].
      destruct (code_relation_total M (E_weq Y X) env) as [r Hr].
      assert (Ha : code_relation M env (E_weq A' A) r).
      { apply (proj2 (expression_equality_graph M env A' A y x r HA' HA)).
        exact (proj1 (expression_equality_graph M env Y X y x r HY HX) Hr). }
      apply (ns_proof_symmetry M env X Y f).
      exact (proj2 (expression_implication_iff M env _ _ h r f Hh Hr)
        (proj1 (expression_implication_iff M env _ _ h r f Hh Ha) Hf)).
  - split; apply ns_proof_weaken;intros f Hf;
      apply (numerical_equality_reflexivity M a f).
    + exact (proj1 (expression_equality_graph M env A A' a a f HA HA') Hf).
    + exact (proj1 (expression_equality_graph M env A' A a a f HA' HA) Hf).
Qed.

Lemma ns_atom_expression M env eq A B a b f :
  code_relation M env A a -> code_relation M env B b ->
  (code_relation M env (E_atom eq A B) f <-> tagged_pair_graph M (named_atom_tag eq) a b f).
Proof.
  intros HA HB.
  assert (He : E_atom eq A B = code_subst (code_parameters A B (CEconst 0) (CEconst 0))
      (E_atom eq (CEvar 0) (CEvar 1))) by (destruct eq;reflexivity).
  rewrite He.
  rewrite (code_subst_graph M env _ (code_parameters a b (zeroM M) (zeroM M))
    (parameter_graphs M env A B (CEconst 0) (CEconst 0) a b (zeroM M) (zeroM M) HA HB eq_refl eq_refl)).
  apply atom_expression_graph.
Qed.

Lemma ns_under_atom M eq x y h a a' b b' f g :
  equality_graph M x y h -> named_replace M x y a a' -> named_replace M x y b b' ->
  tagged_pair_graph M (named_atom_tag eq) a b f ->
  tagged_pair_graph M (named_atom_tag eq) a' b' g ->
  ns_under M h f g /\ ns_under M h g f.
Proof.
  intros Hh HA HB Hf Hg.
  set (env:=x .: y .: a .: a' .: b .: b' .: fun _ => zeroM M).
  assert (Eh : code_relation M env (E_weq (CEvar 0) (CEvar 1)) h).
  { exact (proj2 (expression_equality_graph M env (CEvar 0) (CEvar 1) x y h eq_refl eq_refl) Hh). }
  assert (Ef : code_relation M env (E_atom eq (CEvar 2) (CEvar 4)) f).
  { exact (proj2 (ns_atom_expression M env eq (CEvar 2) (CEvar 4) a b f eq_refl eq_refl) Hf). }
  assert (Eg : code_relation M env (E_atom eq (CEvar 3) (CEvar 5)) g).
  { exact (proj2 (ns_atom_expression M env eq (CEvar 3) (CEvar 5) a' b' g eq_refl eq_refl) Hg). }
  destruct (ns_replace_coordinate M env (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)
    x y a a' eq_refl eq_refl eq_refl eq_refl HA) as [PA PA'].
  destruct (ns_replace_coordinate M env (CEvar 0) (CEvar 1) (CEvar 4) (CEvar 5)
    x y b b' eq_refl eq_refl eq_refl eq_refl HB) as [PB PB'].
  split.
  - apply (proj1 (ns_under_expression M env (E_weq (CEvar 0) (CEvar 1))
      (E_atom eq (CEvar 2) (CEvar 4)) (E_atom eq (CEvar 3) (CEvar 5)) h f g Eh Ef Eg)).
    eapply ns_proof_macro;[|apply ns_macro_atom].
    intros p [<-|[<-|[<-|[]]]];[exact PA|exact PB|apply ns_proof_atom_transport].
  - apply (proj1 (ns_under_expression M env (E_weq (CEvar 0) (CEvar 1))
      (E_atom eq (CEvar 3) (CEvar 5)) (E_atom eq (CEvar 2) (CEvar 4)) h g f Eh Eg Ef)).
    eapply ns_proof_macro;[|apply ns_macro_atom].
    intros p [<-|[<-|[<-|[]]]];[exact PA'|exact PB'|apply ns_proof_atom_transport].
Qed.

