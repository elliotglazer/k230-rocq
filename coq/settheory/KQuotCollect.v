(** Collect the bisimulations witnessing forth/back matching of members. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From ZFC Require Import Z_base.
From K230S Require Import KP0 KP0Use KBase KMarkers KPSeparation KDomain KCollection KQuot KQuotSym.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition forth_match (t x y : term) : form :=
  ∀ (dchild t`[↑] $0 x`[↑] → ∃ (dchild t`[↑]`[↑] $0 y`[↑]`[↑] ∧ deqv t`[↑]`[↑] $1 $0)).
Definition back_match (t x y : term) : form :=
  ∀ (dchild t`[↑] $0 y`[↑] → ∃ (dchild t`[↑]`[↑] $0 x`[↑]`[↑] ∧ deqv t`[↑]`[↑] $0 $1)).
Definition bisim_family (t c : term) : form :=
  ∀ (dchild t`[↑] $0 c`[↑] → dbisim t`[↑] $0).
Definition forth_cover (t x y c : term) : form :=
  ∀ (dchild t`[↑] $0 x`[↑] →
    ∃ (dchild t`[↑]`[↑] $0 c`[↑]`[↑] ∧
      ∃ (dchild t`[↑]`[↑]`[↑] $0 y`[↑]`[↑]`[↑] ∧ App0 $1 $2 $0))).
Definition back_cover (t x y c : term) : form :=
  ∀ (dchild t`[↑] $0 y`[↑] →
    ∃ (dchild t`[↑]`[↑] $0 c`[↑]`[↑] ∧
      ∃ (dchild t`[↑]`[↑]`[↑] $0 x`[↑]`[↑]`[↑] ∧ App0 $1 $0 $2))).

#[global] Arguments forth_match : simpl never.
#[global] Arguments back_match : simpl never.
#[global] Arguments bisim_family : simpl never.
#[global] Arguments forth_cover : simpl never.
#[global] Arguments back_cover : simpl never.
Lemma forth_match_subst t x y sg : (forth_match t x y)[sg] = forth_match t`[sg] x`[sg] y`[sg].
Proof. psubst forth_match. Qed.
Lemma back_match_subst t x y sg : (back_match t x y)[sg] = back_match t`[sg] x`[sg] y`[sg].
Proof. psubst back_match. Qed.
Lemma bisim_family_subst t c sg : (bisim_family t c)[sg] = bisim_family t`[sg] c`[sg].
Proof. psubst bisim_family. Qed.
Lemma forth_cover_subst t x y c sg :
  (forth_cover t x y c)[sg] = forth_cover t`[sg] x`[sg] y`[sg] c`[sg].
Proof. psubst forth_cover. Qed.
Lemma back_cover_subst t x y c sg :
  (back_cover t x y c)[sg] = back_cover t`[sg] x`[sg] y`[sg] c`[sg].
Proof. psubst back_cover. Qed.
#[global] Hint Rewrite forth_match_subst back_match_subst bisim_family_subst forth_cover_subst back_cover_subst : fsub.

(** Output R at 0, input a/b at 1, parameters t and target at 2/3. *)
Definition bisim_forward : form :=
  ∃ (dchild $3 $0 $4 ∧ (dbisim $3 $1 ∧ App0 $1 $2 $0)).
Definition bisim_backward : form :=
  ∃ (dchild $3 $0 $4 ∧ (dbisim $3 $1 ∧ App0 $1 $0 $2)).

Lemma bisim_forward_bounded : fb 4 bisim_forward.
Proof. unfold bisim_forward, dbisim, dchild, App0, OP0, Sing0, Pair0. cbn. lia. Qed.
Lemma bisim_backward_bounded : fb 4 bisim_backward.
Proof. unfold bisim_backward, dbisim, dchild, App0, OP0, Sing0, Pair0. cbn. lia. Qed.

Lemma collect_forth_bisim G (HB : incl KBase G) t x y :
  In (forall_times 3 (kp0 (separation_matrix domain_selector))) G ->
  In (forall_times 6 (kp0 (collection_matrix bisim_forward))) G ->
  G ⊢C raw_empty t -> G ⊢C t ∈' x -> G ⊢C forth_match t x y ->
  G ⊢C ∃ (forth_cover t`[↑] x`[↑] y`[↑] $0 ∧ bisim_family t`[↑] $0).
Proof.
  intros Henv Hinst Hempty Htx Hmatch.
  pose proof (domain_collection _ HB 2 bisim_forward (t .: y .: var) t x
    bisim_forward_bounded Henv Hinst Hempty Htx) as T.
  fex T c HC. unfold collection_profile in HC. fdestr HC Htc Hboth.
  fdestr Hboth Hcov Hsupport. unfold bisim_forward in Hcov, Hsupport.
  simp_in Hcov. simp_in Hsupport.
  fexists c. fsplit.
  - unfold forth_cover. fall a. fintro Ha.
    pose proof Hmatch as HM. unfold forth_match in HM. finst HM a. fmp HM Ha.
    fex HM b HBb. fdestr HBb Hb Heq. unfold deqv in Heq.
    fex Heq r HR. fdestr HR Hbis Har.
    pose proof Hcov as H. finst H a.
    fassert Ha' : (t ∈' a ∧ a ∈' x). { exact Ha. }
    fmp H Ha'.
    match type of H with _ ⊢C ?W → _ => fassert HW : W end.
    { fexists r. fsplit.
      - pose proof Hbis as HD. unfold dbisim in HD. exact (CE1 HD).
      - fexists b. fsplit; [exact Hb|]. fsplit; assumption. }
    fmp H HW. fex H s HS. fdestr HS Hts HSc. fdestr HSc Hsc Hsb.
    fexists s. fsplit; [unfold dchild; fsplit; assumption|].
    fex Hsb b' HBb'. fdestr HBb' Hb' Hrest. fexists b'.
    fsplit; [exact Hb'|exact (CE2 Hrest)].
  - unfold bisim_family. fall r. fintro Hr.
    pose proof Hsupport as H. finst H r. fmp H Hr.
    fex H a HA. pose proof (CE2 HA) as Hex. fex Hex b HBb.
    exact (CE1 (CE2 HBb)).
Qed.

Lemma collect_back_bisim G (HB : incl KBase G) t x y :
  In (forall_times 3 (kp0 (separation_matrix domain_selector))) G ->
  In (forall_times 6 (kp0 (collection_matrix bisim_backward))) G ->
  G ⊢C raw_empty t -> G ⊢C t ∈' y -> G ⊢C back_match t x y ->
  G ⊢C ∃ (back_cover t`[↑] x`[↑] y`[↑] $0 ∧ bisim_family t`[↑] $0).
Proof.
  intros Henv Hinst Hempty Hty Hmatch.
  pose proof (domain_collection _ HB 2 bisim_backward (t .: x .: var) t y
    bisim_backward_bounded Henv Hinst Hempty Hty) as T.
  fex T c HC. unfold collection_profile in HC. fdestr HC Htc Hboth.
  fdestr Hboth Hcov Hsupport. unfold bisim_backward in Hcov, Hsupport.
  simp_in Hcov. simp_in Hsupport.
  fexists c. fsplit.
  - unfold back_cover. fall b. fintro Hb.
    pose proof Hmatch as HM. unfold back_match in HM. finst HM b. fmp HM Hb.
    fex HM a HAa. fdestr HAa Ha Heq. unfold deqv in Heq.
    fex Heq r HR. fdestr HR Hbis Har.
    pose proof Hcov as H. finst H b.
    fassert Hb' : (t ∈' b ∧ b ∈' y). { exact Hb. }
    fmp H Hb'.
    match type of H with _ ⊢C ?W → _ => fassert HW : W end.
    { fexists r. fsplit.
      - pose proof Hbis as HD. unfold dbisim in HD. exact (CE1 HD).
      - fexists a. fsplit; [exact Ha|]. fsplit; assumption. }
    fmp H HW. fex H s HS. fdestr HS Hts HSc. fdestr HSc Hsc Hsa.
    fexists s. fsplit; [unfold dchild; fsplit; assumption|].
    fex Hsa a' HAa'. fdestr HAa' Ha' Hrest. fexists a'.
    fsplit; [exact Ha'|exact (CE2 Hrest)].
  - unfold bisim_family. fall r. fintro Hr.
    pose proof Hsupport as H. finst H r. fmp H Hr.
    fex H b HBb. pose proof (CE2 HBb) as Hex. fex Hex a HAa.
    exact (CE1 (CE2 HAa)).
Qed.
