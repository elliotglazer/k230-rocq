(** Conditional assembly of the atom interface needed by the mixed
    quotation induction. The four raw KLogic laws below are explicit inputs,
    not proofs of those laws. Every input is a numerical proof under the
    exact raw-empty marker, with explicit atom graphs and safe bases. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  NumericalProofs NumericalEquivalence NumericalContexts NumericalEnvironments
  ProofTemplates TemplatePropositional ContextualProofs ContextualEquivalence
  ContextualPropositional StableContextSupport SupportedQuotientEnvironments
  QuotationPayloads QuotationAtomRebase MixedQuotationCongruence.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List setoid_ring.Ring.
Unset Implicit Arguments.

Definition raw_empty_marker_graph M t name marker :=
  coding_lt M (zeroM M) name /\ coding_lt M t name /\
  code_relation M (t .: name .: fun _=>zeroM M)
    (E_wal (CEvar 1) (E_wn (E_wel (CEvar 1) (CEvar 0)))) marker.

(** A curried finite propositional consequence, under the raw marker.
    It is expressed through the actual numerical graph of A -> B -> C. *)
Definition raw_marker_binary_law M marker a b c :=
  forall h, code_relation M (a .: b .: c .: fun _=>zeroM M)
    (E_wim (CEvar 0) (E_wim (CEvar 1) (CEvar 2))) h ->
    numerical_implies M marker h.

Record raw_quotient_atom_laws M t marker := {
  raw_deqv_symmetry :
    forall x y k a b h,
    quotient_pair_safe M t x y k ->
    quotation_atom M true x y t k a -> quotation_atom M true y x t k b ->
    implication_graph M a b h -> numerical_implies M marker h;
  raw_deqv_transitivity :
    forall x y z k a b c,
    quotient_pair_safe M t x y k -> quotient_pair_safe M t y z k ->
    quotation_atom M true x y t k a -> quotation_atom M true y z t k b ->
    quotation_atom M true x z t k c -> raw_marker_binary_law M marker a b c;
  raw_dmem_left_transport :
    forall x x' y k a b c,
    quotient_pair_safe M t x x' k -> quotient_pair_safe M t x y k ->
    quotation_atom M true x x' t k a -> quotation_atom M false x y t k b ->
    quotation_atom M false x' y t k c -> raw_marker_binary_law M marker a b c;
  raw_dmem_right_transport :
    forall x y y' k a b c,
    quotient_pair_safe M t y y' k -> quotient_pair_safe M t x y k ->
    quotation_atom M true y y' t k a -> quotation_atom M false x y t k b ->
    quotation_atom M false x y' t k c -> raw_marker_binary_law M marker a b c
}.

Lemma raw_marker_binary_apply M cb cc cn marker a b c :
  stable_context_support M cb cc cn marker ->
  stable_context_support M cb cc cn a ->
  raw_marker_binary_law M marker a b c ->
  contextual_implies M cb cc cn b c.
Proof.
  intros HM HA HL. set (rho:=a .: b .: c .: fun _=>zeroM M).
  apply (proj1 (contextual_implies_expression M cb cc cn rho
    (CEvar 1) (CEvar 2) b c eq_refl eq_refl)).
  intros f HF. apply stable_context_support_here.
  apply (stable_context_support_derivation M cb cc cn rho
    (CEvar 0 :: E_wim (CEvar 0) (E_wim (CEvar 1) (CEvar 2)) :: nil)
    (E_wim (CEvar 1) (CEvar 2))).
  - intros e [<-|[<-|[]]] q HQ.
    + change (q=a) in HQ. now subst q.
    + exact (stable_context_support_implies M cb cc cn marker q (HL q HQ) HM).
  - eapply dmp with (a:=CEvar 0);apply dhyp;cbn;tauto.
  - exact HF.
Qed.

Lemma raw_laws_stable_symmetry M cb cc cn t marker :
  stable_context_support M cb cc cn marker ->
  raw_quotient_atom_laws M t marker ->
  stable_quotient_atom_symmetry M cb cc cn t.
Proof.
  intros HM HL. apply (stable_quotient_atom_symmetry_from_marker M cb cc cn t marker HM).
  exact (raw_deqv_symmetry M t marker HL).
Qed.

(** All names needed by a transport fit below one common allocation base. *)
Definition quotient_four_safe M t x y x' y' k :=
  coding_lt M (zeroM M) k /\ coding_lt M t k /\
  coding_lt M x k /\ coding_lt M y k /\ coding_lt M x' k /\ coding_lt M y' k.
Section CommonBase.
Variable M : Model.
Add Ring raw_atom_ring : (model_semiring M).
Lemma quotient_four_safe_total t x y x' y' :
  exists k,quotient_four_safe M t x y x' y' k.
Proof.
  exists (succM M (addM M t (addM M x (addM M y (addM M x' y'))))).
  split;[apply coding_zero_lt_succ|]. split.
  - exists (addM M x (addM M y (addM M x' y'))). reflexivity.
  - split.
    + exists (addM M t (addM M y (addM M x' y'))). f_equal. ring.
    + split.
      * exists (addM M t (addM M x (addM M x' y'))). f_equal. ring.
      * split.
        -- exists (addM M t (addM M x (addM M y y'))). f_equal. ring.
        -- exists (addM M t (addM M x (addM M y x'))). f_equal. ring.
Qed.
End CommonBase.

Lemma raw_atom_rebase M equality t x y k l f g :
  quotient_pair_safe M t x y k -> quotient_pair_safe M t x y l ->
  quotation_atom M equality x y t k f -> quotation_atom M equality x y t l g ->
  numerical_equivalent M f g.
Proof.
  intros [Hk0 [Hkt [Hkx Hky]]] [Hl0 [Hlt [Hlx Hly]]] HF HG.
  exact (quotation_atom_rebase M equality x y t k l f g
    Hk0 Hl0 Hkx Hky Hkt Hlx Hly Hlt HF HG).
Qed.

Lemma raw_supported_left_transport M cb cc cn t marker equality x x' y k f g :
  stable_context_support M cb cc cn marker -> raw_quotient_atom_laws M t marker ->
  quotient_pair_safe M t x x' k -> quotient_pair_safe M t x y k ->
  supported_quotient_pair M cb cc cn t x x' ->
  quotation_atom M equality x y t k f -> quotation_atom M equality x' y t k g ->
  contextual_implies M cb cc cn f g.
Proof.
  intros HM HL Hxx Hxy [Hsame|HE] HF HG.
  - subst x'. assert (f=g) by exact (quotation_atom_functional M equality x y t k f g HF HG).
    subst g. exact (proj1 (contextual_equivalence_global M cb cc cn f f (numerical_equivalent_refl M f))).
  - destruct equality.
    + destruct (quotation_atom_total M true x' x t k) as [q HQ].
      pose proof (supported_quotient_pair_sym M cb cc cn t x x'
        (raw_laws_stable_symmetry M cb cc cn t marker HM HL) (or_intror HE)) as HRev.
      destruct HRev as [Hsame|HR].
      * subst x'. assert (f=g) by exact (quotation_atom_functional M true x y t k f g HF HG).
        subst g. exact (proj1 (contextual_equivalence_global M cb cc cn f f (numerical_equivalent_refl M f))).
      * apply (raw_marker_binary_apply M cb cc cn marker q f g HM
          (HR k q (quotient_pair_safe_sym M t x x' k Hxx) HQ)).
        exact (raw_deqv_transitivity M t marker HL x' x y k q f g
          (quotient_pair_safe_sym M t x x' k Hxx) Hxy HQ HF HG).
    + destruct (quotation_atom_total M true x x' t k) as [q HQ].
      apply (raw_marker_binary_apply M cb cc cn marker q f g HM (HE k q Hxx HQ)).
      exact (raw_dmem_left_transport M t marker HL x x' y k q f g Hxx Hxy HQ HF HG).
Qed.

Lemma raw_supported_right_transport M cb cc cn t marker equality x y y' k f g :
  stable_context_support M cb cc cn marker -> raw_quotient_atom_laws M t marker ->
  quotient_pair_safe M t y y' k -> quotient_pair_safe M t x y k ->
  supported_quotient_pair M cb cc cn t y y' ->
  quotation_atom M equality x y t k f -> quotation_atom M equality x y' t k g ->
  contextual_implies M cb cc cn f g.
Proof.
  intros HM HL Hyy Hxy [Hsame|HE] HF HG.
  - subst y'. assert (f=g) by exact (quotation_atom_functional M equality x y t k f g HF HG).
    subst g. exact (proj1 (contextual_equivalence_global M cb cc cn f f (numerical_equivalent_refl M f))).
  - destruct (quotation_atom_total M true y y' t k) as [q HQ].
    destruct equality.
    + (** Transitivity is curried in the order f,q. Swap its premises
          by a finite propositional derivation before consuming q. *)
      set (rho:=q .: f .: g .: fun _=>zeroM M).
      apply (proj1 (contextual_implies_expression M cb cc cn rho
        (CEvar 1) (CEvar 2) f g eq_refl eq_refl)).
      intros h HH. apply stable_context_support_here.
      apply (stable_context_support_derivation M cb cc cn rho
        (CEvar 0 :: E_wim (CEvar 1) (E_wim (CEvar 0) (CEvar 2)) :: nil)
        (E_wim (CEvar 1) (CEvar 2))).
      * intros e [<-|[<-|[]]] v HV.
        -- change (v=q) in HV. subst v. exact (HE k q Hyy HQ).
        -- apply (stable_context_support_implies M cb cc cn marker v);[|exact HM].
           apply (raw_deqv_transitivity M t marker HL x y y' k f q g Hxy Hyy HF HQ HG v).
           unfold rho in HV. exact HV.
      * apply template_deduction. eapply dmp with (a:=CEvar 0).
        -- eapply dmp with (a:=CEvar 1);apply dhyp;cbn;tauto.
        -- apply dhyp;cbn;tauto.
      * exact HH.
    + apply (raw_marker_binary_apply M cb cc cn marker q f g HM (HE k q Hyy HQ)).
      exact (raw_dmem_right_transport M t marker HL x y y' k q f g Hyy Hxy HQ HF HG).
Qed.

Lemma raw_supported_atom_transport M cb cc cn t marker equality x y x' y' k f g :
  stable_context_support M cb cc cn marker -> raw_quotient_atom_laws M t marker ->
  quotient_four_safe M t x y x' y' k ->
  supported_quotient_pair M cb cc cn t x x' -> supported_quotient_pair M cb cc cn t y y' ->
  quotation_atom M equality x y t k f -> quotation_atom M equality x' y' t k g ->
  contextual_implies M cb cc cn f g.
Proof.
  intros HM HL [H0 [Ht [Hx [Hy [Hx' Hy']]]]] HE HF HQ HR.
  destruct (quotation_atom_total M equality x' y t k) as [q Hq].
  apply (mixed_contextual_implication_trans M cb cc cn f q g).
  - apply (raw_supported_left_transport M cb cc cn t marker equality x x' y k f q HM HL);
      try assumption;repeat split;assumption.
  - apply (raw_supported_right_transport M cb cc cn t marker equality x' y y' k q g HM HL);
      try assumption;repeat split;assumption.
Qed.

Theorem raw_laws_uniform_mixed_atom_equivalence M cb cc cn t marker marker_name :
  raw_empty_marker_graph M t marker_name marker ->
  stable_context_support M cb cc cn marker -> raw_quotient_atom_laws M t marker ->
  uniform_mixed_atom_equivalence M t cb cc cn.
Proof.
  intros HMarker HM HL equality k l x y x' y' f g Hk Hl Hx Hy HF HG.
  destruct (quotient_four_safe_total M t x y x' y') as [r Hr].
  destruct Hr as [H0 [Ht [Hrx [Hry [Hrx' Hry']]]]].
  destruct (quotation_atom_total M equality x y t r) as [f' HF'].
  destruct (quotation_atom_total M equality x' y' t r) as [g' HG'].
  assert (EF : contextual_equivalence M cb cc cn f f').
  { apply contextual_equivalence_global.
    apply (raw_atom_rebase M equality t x y k r f f' Hk);try assumption;repeat split;assumption. }
  assert (EG : contextual_equivalence M cb cc cn g' g).
  { apply contextual_equivalence_global.
    apply (raw_atom_rebase M equality t x' y' r l g' g);try assumption;repeat split;assumption. }
  apply (mixed_contextual_equivalence_trans M cb cc cn f f' g EF).
  apply (mixed_contextual_equivalence_trans M cb cc cn f' g' g);[|exact EG].
  split.
  - apply (raw_supported_atom_transport M cb cc cn t marker equality x y x' y' r f' g' HM HL);
      try assumption;repeat split;assumption.
  - apply (raw_supported_atom_transport M cb cc cn t marker equality x' y' x y r g' f' HM HL).
    + repeat split;assumption.
    + exact (supported_quotient_pair_sym M cb cc cn t x x'
        (raw_laws_stable_symmetry M cb cc cn t marker HM HL) Hx).
    + exact (supported_quotient_pair_sym M cb cc cn t y y'
        (raw_laws_stable_symmetry M cb cc cn t marker HM HL) Hy).
    + exact HG'.
    + exact HF'.
Qed.

Theorem raw_laws_mixed_quotation_congruence M cb cc cn t marker marker_name :
  raw_empty_marker_graph M t marker_name marker ->
  stable_context_support M cb cc cn marker -> raw_quotient_atom_laws M t marker ->
  forall source,mixed_quotation_property M t cb cc cn source.
Proof.
  intros HE HM HL. apply numerical_mixed_quotation_congruence.
  exact (raw_laws_uniform_mixed_atom_equivalence M cb cc cn t marker marker_name HE HM HL).
Qed.

Print Assumptions raw_marker_binary_apply.
Print Assumptions raw_supported_atom_transport.
Print Assumptions raw_laws_uniform_mixed_atom_equivalence.
Print Assumptions raw_laws_mixed_quotation_congruence.
