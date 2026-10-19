(** Raw relation codes. The endpoint-injectivity proof is reused unchanged
    from the pinned reference and requires only the four equality axioms. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From ZFC Require Import Z_base.
From M254S Require Import S_raw.
From K230S Require Import KP0 KP0Use KPRaw KPPair KBase KMarkers KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma KBase_ordered_pair G (HB : incl KBase G) x y :
  G ⊢C ∃ OP0 x`[↑] y`[↑] $0.
Proof.
  pose proof (KBase_eq _ HB) as HE.
  fobtain (KBase_singleton _ HB x) as s Hs.
  fobtain (KBase_pair _ HB x y) as d Hd.
  fobtain (KBase_pair _ HB s d) as c Hc.
  fexists c. unfold OP0. fsplit; [fsplit|].
  - fexists s. fsplit; [exact (pair0_inl HE s d c Hc)|exact Hs].
  - fexists d. fsplit; [exact (pair0_inr HE s d c Hc)|exact Hd].
  - fall e. fintro He. pose proof (pair0_el HE s d c e Hc He) as E.
    fcases E Es Ed.
    + fleft. frewE Es (Sing0 x`[↑] $0). exact Hs.
    + fright. frewE Ed (Pair0 x`[↑] y`[↑] $0). exact Hd.
Qed.

Lemma ordered_pair_no_empty_member G (HE : incl EqAx G) t x y c :
  G ⊢C raw_empty t -> G ⊢C OP0 x y c -> G ⊢C t ∈' c -> G ⊢C ⊥.
Proof.
  intros Hempty Hcode Htc. unfold raw_empty in Hempty. finst Hempty x.
  pose proof (op0_kinds HE x y c t Hcode Htc) as Hkind.
  fcases Hkind Hs Hp.
  - exact (IE Hempty (sing0_in HE x t Hs)).
  - exact (IE Hempty (pair0_inl HE x y t Hp)).
Qed.

Definition codes_over (w d : term) : form :=
  ∀ ($0 ∈' w`[↑] → ∀ ($0 ∈' w`[↑]`[↑] →
    ∀ (OP0 $2 $1 $0 → $0 ∈' d`[↑]`[↑]`[↑]))).

#[global] Arguments codes_over : simpl never.
Lemma codes_over_subst w d sg : (codes_over w d)[sg] = codes_over w`[sg] d`[sg].
Proof. psubst codes_over. Qed.
#[global] Hint Rewrite codes_over_subst : fsub.

Lemma KBase_code_bound G (HB : incl KBase G) t w :
  G ⊢C raw_empty t -> G ⊢C ∃ (t`[↑] ∈' $0 ∧ codes_over w`[↑] $0).
Proof.
  intros Hempty. pose proof (KBase_eq _ HB) as HE.
  fobtain (KBase_power _ HB w) as p HP.
  fobtain (KBase_power _ HB p) as d HD.
  fexists d. fsplit.
  - pose proof HD as H. finst H t. apply (iff_r _ _ _ H).
    unfold raw_subset, raw_empty in *. fall z. fintro Hzt.
    finst Hempty z. fabsurd. exact (IE Hempty Hzt).
  - unfold codes_over. fall x. fintro Hx. fall y. fintro Hy.
    fall c. fintro Hc. finst HD c. apply (iff_r _ _ _ HD).
    unfold raw_subset. fall e. fintro He. finst HP e. apply (iff_r _ _ _ HP).
    unfold raw_subset. fall z. fintro Hz.
    pose proof (op0_kinds HE x y c e Hc He) as Hkind.
    fcases Hkind Hs Hp.
    + pose proof (sing0_el HE x e z Hs Hz) as E. fmemE.
    + pose proof (pair0_el HE x y e z Hp Hz) as E. fcases E Eleft Eright; fmemE.
Qed.

Definition raw_ordered_pair_axiom : form := ∀ ∀ ∃ OP0 $2 $1 $0.

Theorem K0_proves_raw_ordered_pair : K0 ⊢TC raw_ordered_pair_axiom.
Proof.
  exists KBase. split; [exact KBase_ok|]. unfold raw_ordered_pair_axiom.
  fall x. fall y.
  match goal with |- ?G ⊢C _ =>
    assert (HB : incl KBase G) by (intros a Ha; exact Ha)
  end.
  exact (KBase_ordered_pair _ HB x y).
Qed.

Corollary KPrimeOrd_proves_raw_ordered_pair : KPrimeOrd ⊢TC raw_ordered_pair_axiom.
Proof. apply K0_derivation_to_KPrimeOrd, K0_proves_raw_ordered_pair. Qed.
