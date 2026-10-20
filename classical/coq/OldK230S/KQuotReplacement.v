(** Replacement for translated formulas functional modulo bisimulation. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From OldK230S Require Import KP0 KP0Use KBase KMarkers KDomain KPSeparation KCollection KQuot KQuotFormula KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma qtrans_binary_inv G (HL : incl KLogic G) t phi (sg : nat -> term) x x' y y' :
  G ⊢C raw_empty t -> (x = x' \/ G ⊢C deqv t x x') ->
  (y = y' \/ G ⊢C deqv t y y') ->
  G ⊢C qtrans t phi[x .: y .: sg] -> G ⊢C qtrans t phi[x' .: y' .: sg].
Proof.
  intros Hempty Hx Hy H. eapply (qtrans_mixed_inv phi _ t (x .: y .: sg) (x' .: y' .: sg)); eauto.
  intros [|[|k]]; cbn; [exact Hx|exact Hy|left; reflexivity].
Qed.

(** Output/input are 0/1, marker 2, then the original parameters. *)
Definition replacement_predicate (phi : form) : form :=
  qtrans $2 phi[$0 .: $1 .: (fun k => $(3 + k))].
Lemma replacement_predicate_bounded n phi : fb (S (S n)) phi ->
  fb (S (S (S n))) (replacement_predicate phi).
Proof.
  intros H. unfold replacement_predicate. apply qtrans_bounded; [|cbn; lia].
  eapply fb_subst; [exact H|]. intros [|[|k]] Hk; cbn; lia.
Qed.

Definition qfunctional (t a : term) (phi : form) (sg : nat -> term) : form :=
  ∀ ((t`[↑] ∈' $0 ∧ dmem t`[↑] $0 a`[↑]) →
    ∀ (t`[↑]`[↑] ∈' $0 → ∀ (t`[↑]`[↑]`[↑] ∈' $0 →
      qtrans t`[↑]`[↑]`[↑] phi[$1 .: $2 .: (fun k => (sg k)`[↑]`[↑]`[↑])] →
      qtrans t`[↑]`[↑]`[↑] phi[$0 .: $2 .: (fun k => (sg k)`[↑]`[↑]`[↑])] →
      deqv t`[↑]`[↑]`[↑] $1 $0))).

Definition qimage (t a c : term) (phi : form) (sg : nat -> term) : form :=
  t ∈' c ∧ ∀ (t`[↑] ∈' $0 →
    (dmem t`[↑] $0 c`[↑] ↔
      ∃ ((t`[↑]`[↑] ∈' $0 ∧ dmem t`[↑]`[↑] $0 a`[↑]`[↑]) ∧
        qtrans t`[↑]`[↑] phi[$1 .: $0 .: (fun k => (sg k)`[↑]`[↑])]))).

Lemma qreplacement_exists G (HL : incl KLogic G) n phi (sg : nat -> term) t a :
  fb (S (S n)) phi ->
  In (forall_times 3 (kp0 (separation_matrix domain_selector))) G ->
  In (forall_times (S (S (S (S (S n))))) (kp0 (collection_matrix (replacement_predicate phi)))) G ->
  G ⊢C raw_empty t -> G ⊢C t ∈' a -> G ⊢C qfunctional t a phi sg ->
  G ⊢C ∃ qimage t`[↑] a`[↑] $0 phi (fun k => (sg k)`[↑]).
Proof.
  intros Hfb Henv Hinst Hempty Hta Hfun.
  pose proof (domain_collection _ (KLogic_base _ HL) (S n) (replacement_predicate phi)
    (t .: sg) t a (replacement_predicate_bounded n phi Hfb) Henv Hinst Hempty Hta) as T.
  fex T c HC. unfold collection_profile in HC. fdestr HC Htc Hboth.
  fdestr Hboth Hcov Hsupport. unfold replacement_predicate in Hcov, Hsupport.
  simp_in Hcov. simp_in Hsupport.
  fexists c. unfold qimage. fsplit; [exact Htc|]. fall y. fintro Hty. fsplit.
  - fintro Hyc. unfold dmem in Hyc. fex Hyc z HZ. fdestr HZ Hz Hyz.
    unfold dchild in Hz. fdestr Hz Htz Hzc.
    pose proof Hsupport as H. finst H z.
    fassert Hz' : (t ∈' z ∧ z ∈' c). { fsplit; assumption. }
    fmp H Hz'. fex H x HX. fdestr HX Hx Hphi.
    fdestr Hx Htx Hxa.
    fassert Hphizx : (qtrans t phi[z .: x .: sg]). { kconv Hphi. }
    pose proof (KLogic_sym _ HL t y z Hempty Hyz) as Hzy.
    pose proof (qtrans_binary_inv _ HL t phi sg z y x x Hempty
      (or_intror Hzy) (or_introl eq_refl) Hphizx) as Hphiyx.
    fexists x. fsplit.
    + fsplit; [exact Htx|]. unfold dmem. fexists x. fsplit.
      * unfold dchild. fsplit; assumption.
      * exact (KLogic_refl _ HL t x Hempty Htx).
    + kconv Hphiyx.
  - fintro Hex. fex Hex x HX. fdestr HX Hx Hphi.
    fdestr Hx Htx Hxa.
    fassert Hphiyx : (qtrans t phi[y .: x .: sg]). { kconv Hphi. }
    unfold dmem in Hxa. fex Hxa u HU. fdestr HU Hu Hxu.
    unfold dchild in Hu. fdestr Hu Htu Hua.
    pose proof (qtrans_binary_inv _ HL t phi sg y y x u Hempty
      (or_introl eq_refl) (or_intror Hxu) Hphiyx) as Hphiyu.
    pose proof Hcov as H. finst H u.
    fassert Hu' : (t ∈' u ∧ u ∈' a). { fsplit; assumption. }
    fmp H Hu'.
    match type of H with _ ⊢C ?W → _ => fassert HW : W end.
    { fexists y. fsplit; [exact Hty|]. kconv Hphiyu. }
    fmp H HW. fex H z HZ. fdestr HZ Htz Hrest. fdestr Hrest Hzc Hphiz.
    fassert Hphizu : (qtrans t phi[z .: u .: sg]). { kconv Hphiz. }
    fassert Hua' : (dmem t u a).
    { unfold dmem. fexists u. fsplit; [unfold dchild; fsplit; assumption|].
      exact (KLogic_refl _ HL t u Hempty Htu). }
    pose proof Hfun as F. unfold qfunctional in F. finst F u.
    fassert Harg : (t ∈' u ∧ dmem t u a). { fsplit; assumption. }
    fmp F Harg. finst F y. fmp F Hty. finst F z. fmp F Htz.
    fassert HFy : (qtrans t phi[y .: u .: sg]). { exact Hphiyu. }
    fassert HFz : (qtrans t phi[z .: u .: sg]). { exact Hphizu. }
    match type of F with _ ⊢C ?P → _ => fassert HFy' : P end.
    { kconv HFy. }
    fmp F HFy'.
    match type of F with _ ⊢C ?P → _ => fassert HFz' : P end.
    { kconv HFz. }
    fmp F HFz'.
    unfold dmem. fexists z. fsplit; [unfold dchild; fsplit; assumption|exact F].
Qed.

Definition qreplacement_statement (phi : form) : form :=
  ∀ ∀ (raw_empty $0 → $0 ∈' $1 → qfunctional $0 $1 phi (fun k => $(2 + k)) →
    ∃ qimage $1 $2 $0 phi (fun k => $(3 + k))).

Theorem K0_proves_qreplacement n phi : fb (S (S n)) phi ->
  K0 ⊢TC forall_times n (qreplacement_statement phi).
Proof.
  intros Hfb.
  set (ei := forall_times 3 (kp0 (separation_matrix domain_selector))).
  set (ri := forall_times (S (S (S (S (S n))))) (kp0 (collection_matrix (replacement_predicate phi)))).
  set (B0 := KLogic ++ [ei; ri]).
  assert (HL : incl KLogic B0) by (intros b Hb; apply in_or_app; now left).
  assert (HEI : In ei B0) by (apply in_or_app; right; now left).
  assert (HRI : In ri B0) by (apply in_or_app; right; right; now left).
  exists B0. split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[<-|[]]]].
    + apply KLogic_ok, Hb.
    + apply K0_instance, kp0_closed, separation_matrix_bounded, domain_selector_bounded.
    + apply K0_instance, kp0_closed, collection_matrix_bounded, replacement_predicate_bounded, Hfb.
  - apply ft_intro. intros sg. unfold qreplacement_statement. cbn.
    fall a. fall t.
    match goal with |- ?G ⊢C _ =>
      assert (HL' : incl KLogic G) by exact HL;
      assert (HEI' : In ei G) by exact HEI;
      assert (HRI' : In ri G) by exact HRI
    end.
    fintro Hempty. fintro Hta. fintro Hfun.
    fassert Hfun' : (qfunctional t a phi sg).
    { unfold qfunctional in Hfun |- *. cbn. kconv Hfun. }
    pose proof (qreplacement_exists _ HL' n phi sg t a Hfb HEI' HRI' Hempty Hta Hfun') as T.
    unfold qimage in T |- *. cbn. kconv T.
Qed.

Corollary KPrimeOrd_proves_qreplacement n phi : fb (S (S n)) phi ->
  KPrimeOrd ⊢TC forall_times n (qreplacement_statement phi).
Proof. intros H. apply K0_derivation_to_KPrimeOrd, K0_proves_qreplacement, H. Qed.
