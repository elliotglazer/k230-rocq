(** Finite propositional proof transformations, parameterized by numerical
    expressions and K-bundle inequality guards. Adapted structurally from
    Comp_Prop230.v; all outputs are ProofTemplates.template_proof objects.
    Source SHA256: e17ecf4b1173df47e658cd99861c42035aa2fb092a59688ce797646130291119. *)
From PAModel Require Import CodeExpressions ProofTemplates TemplateCD.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Section PropositionalTemplates.
Variable Guards : list (code_expr * code_expr).
Lemma template_I p : (template_proof Guards) (E_wim p p).
Proof.
  exact (TP_mp _ _ (template_K p p) (TP_mp _ _ (template_K p (E_wim p p)) (template_S p (E_wim p p) p))).
Qed.

(** ** Hilbert derivations with hypotheses, deduction theorem *)
Inductive template_derivation (Delta : list code_expr) : code_expr -> Prop :=
  | dhyp n : In n Delta -> template_derivation Delta n
  | dthm n : (template_proof Guards) n -> template_derivation Delta n
  | dmp a b : template_derivation Delta (E_wim a b) -> template_derivation Delta a -> template_derivation Delta b.

Lemma template_deduction Delta h a : template_derivation (h :: Delta) a -> template_derivation Delta (E_wim h a).
Proof.
  induction 1 as [n [<-|Hn] | n Hn | a b _ IH1 _ IH2].
  - apply dthm. apply template_I.
  - apply (dmp _ n); [apply dthm, template_K | now apply dhyp].
  - apply (dmp _ n); [apply dthm, template_K | now apply dthm].
  - apply (dmp _ (E_wim h a)); [|exact IH2].
    apply (dmp _ (E_wim h (E_wim a b))); [apply dthm, template_S | exact IH1].
Qed.

Lemma template_discharge a : template_derivation [] a -> (template_proof Guards) a.
Proof.
  induction 1 as [n [] | n Hn | a b _ IH1 _ IH2]; [exact Hn | exact (TP_mp _ _ IH2 IH1)].
Qed.

Lemma template_weaken Delta Delta' a : template_derivation Delta a -> incl Delta Delta' -> template_derivation Delta' a.
Proof.
  intros Hd Hi. induction Hd as [n Hn | n Hn | x y _ IH1 _ IH2];
    [apply dhyp; auto | now apply dthm | eapply dmp; eauto].
Qed.

Ltac hyp := apply dhyp; simpl; tauto.

(** ** Explosion and classical propositional logic *)
Lemma template_F a : (template_proof Guards) (E_wim (CEconst 1) a).
Proof.
  (* rho6 (CEconst 0) a : (E.(CEconst 0) A.(CEconst 0) a) -> a,  and  F -> E.(CEconst 0) A.(CEconst 0) a  by K *)
  apply template_discharge. apply template_deduction.
  apply (dmp _ (E_wex (CEconst 0) (E_wal (CEconst 0) a))); [apply dthm, template_r6|].
  unfold E_wex, E_wn. apply (dmp _ (CEconst 1)); [apply dthm, template_K | hyp].
Qed.

Lemma template_DNE a : (template_proof Guards) (E_wim (E_wim (E_wim a (CEconst 1)) (CEconst 1)) a).
Proof.
  (* Peirce ((a -> F) -> a) -> a,  and  ((a->F)->F) -> ((a->F) -> a) *)
  apply template_discharge. apply template_deduction.
  apply (dmp _ (E_wim (E_wim a (CEconst 1)) a)); [apply dthm, template_P|].
  apply template_deduction. apply (dmp _ (CEconst 1)); [apply dthm, template_F|].
  apply (dmp _ (E_wim a (CEconst 1))); hyp.
Qed.

(** ** Conjunction (E_wa a b = (a -> (b -> F)) -> F) *)
Lemma template_der_andl Delta a b : template_derivation Delta (E_wa a b) -> template_derivation Delta a.
Proof.
  intro H. apply (dmp _ (E_wim (E_wim a (CEconst 1)) (CEconst 1))); [apply dthm, template_DNE|].
  apply template_deduction. apply (dmp _ (E_wim a (E_wn b))); [apply (template_weaken _ _ _ H); intros ? ?; simpl; tauto|].
  apply template_deduction. apply (dmp _ (CEconst 1)); [apply dthm, template_F|]. apply (dmp _ a); hyp.
Qed.

Lemma template_der_andr Delta a b : template_derivation Delta (E_wa a b) -> template_derivation Delta b.
Proof.
  intro H. apply (dmp _ (E_wim (E_wim b (CEconst 1)) (CEconst 1))); [apply dthm, template_DNE|].
  apply template_deduction. apply (dmp _ (E_wim a (E_wn b))); [apply (template_weaken _ _ _ H); intros ? ?; simpl; tauto|].
  apply template_deduction. hyp.
Qed.

Lemma template_der_andi Delta a b : template_derivation Delta a -> template_derivation Delta b -> template_derivation Delta (E_wa a b).
Proof.
  intros Ha Hb. unfold E_wa, E_wn. apply template_deduction.
  apply (dmp _ b); [|apply (template_weaken _ _ _ Hb); intros ? ?; simpl; tauto].
  apply (dmp _ a); [hyp | apply (template_weaken _ _ _ Ha); intros ? ?; simpl; tauto].
Qed.

(** ** The lprov axioms *)
Lemma template_B3 a b : (template_proof Guards) (E_wim a (E_wim (E_wim a (CEconst 1)) b)).
Proof.
  apply template_discharge. do 2 apply template_deduction.
  apply (dmp _ (CEconst 1)); [apply dthm, template_F|]. apply (dmp _ a); hyp.
Qed.

Lemma template_B6a x y z : In (z,x) Guards -> In (z,y) Guards ->
  (template_proof Guards) (E_wa (E_wim (E_weq x y) (E_wal z (E_weq x y))) (E_wim (E_wel x y) (E_wal z (E_wel x y)))).
Proof.
  intros H1 H2. pose proof (TP_bundle x y z H1 H2) as HB.
  unfold E_bundle in HB. apply template_discharge.
  assert (V : template_derivation [] (E_wa (E_wim (E_wel x y) (E_wal z (E_wel x y))) (E_wim (E_weq x y) (E_wal z (E_weq x y)))))
    by (eapply template_der_andr; apply dthm; exact HB).
  apply template_der_andi; [eapply template_der_andr | eapply template_der_andl]; exact V.
Qed.


End PropositionalTemplates.

Print Assumptions template_F.
Print Assumptions template_DNE.
Print Assumptions template_B6a.
