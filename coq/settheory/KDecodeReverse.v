(** Validation of the exact decoded core when its two active names differ.
    Freshness is free-variable freshness, including the exceptional matrix
    codes zero and one.  This is not the relative-falsity machine bridge. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic Std_dB Std_tr Std_alpha Std_F Std_iface
  Std_setnd Std_setbase Std_breq Std_brnd.
From K230S Require Import KP0Use KPRaw KPSeed KPrimeCore KDecodeBundle KDecodeAbstract.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Theorem ordinary_to_named_source G q a b k rho :
  a <> b -> k <> a -> k <> b -> fr k q = false ->
  G ⊢C (kprime_core (abstract_matrix a b q))[rho] ->
  G ⊢C dB rho (KCore a b k q).
Proof.
  intros Hab Hka Hkb Hfresh Hsource.
  unfold kprime_core, output_root in Hsource. simp_in Hsource.
  finst Hsource (rho a) (rho b).
  fex Hsource C HC. fdestr HC Hroot Hclosure.
  unfold KCore. apply (dB_exI _ _ _ C). rewrite (decode_env_root a b k rho C).
  apply dB_andI.
  - apply II. ctx_push Hq. rewrite decode_env_matrix in Hq by exact Hfresh.
    match goal with |- ?G0 ⊢C _ =>
      change (G0 ⊢C dB (decode_env a b k rho (rho b) (rho a) C) (Wel b k)) end.
    rewrite decode_env_member by exact Hkb.
    apply (IE Hroot). kconv Hq.
  - apply dB_allI. intros u. rewrite decode_env_output by exact Hkb.
    apply II. ctx_push Hu.
    match type of Hu with ?G0 ⊢C _ =>
      change (G0 ⊢C dB (decode_env a b k rho u (rho a) C) (Wel b k)) in Hu end.
    rewrite decode_env_member in Hu by exact Hkb.
    unfold emitted_closure in Hclosure. simp_in Hclosure.
    finst Hclosure u. fmp Hclosure Hu.
    fex Hclosure p Hp. fdestr Hp HpPhi HpReq.
    apply (dB_exI _ _ _ p). rewrite decode_env_input by assumption.
    apply dB_andI.
    + rewrite decode_env_matrix by exact Hfresh. kconv HpPhi.
    + apply dB_allI. intros v. rewrite decode_env_input by assumption.
      apply II. ctx_push Hv.
      match type of Hv with ?G0 ⊢C _ =>
        change (G0 ⊢C dB (decode_env a b k rho u v C) (KSubset a b k)) in Hv end.
      rewrite decode_env_subset in Hv by assumption.
      finst HpReq v. fmp HpReq Hv.
      apply (dB_allI _ b (Wim q (Wex b (Wa q (Wel b k))))). intros z.
      rewrite decode_env_output by exact Hkb.
      apply II. ctx_push Hz. rewrite decode_env_matrix in Hz by exact Hfresh.
      finst HpReq z.
      match type of HpReq with _ ⊢C ?P → _ => fassert Hz' : P end.
      { kconv Hz. }
      fmp HpReq Hz'. fex HpReq w Hw. fdestr Hw HwPhi HwMem.
      apply (dB_exI _ _ _ w). rewrite decode_env_output by exact Hkb.
      apply dB_andI.
      * rewrite decode_env_matrix by exact Hfresh. kconv HwPhi.
      * rewrite decode_env_member by exact Hkb. exact HwMem.
Qed.
