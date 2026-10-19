(** Extraction of the ordinary output-root schema from an actual decoded
    source instance.  A closed named source instance can be instantiated at
    every environment; no semantic completeness or choice is used. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic Std_dB Std_tr Std_alpha Std_gen Std_F Std_iface
  Std_iface2 Std_setnd Std_setbase Std_breq Std_brnd.
From K230S Require Import KP0Use KPRaw KPSeed KPrimeCore KCode230 KDecoder230
  KDecodeBundle KDecodeEncode KDecodeTranslate KDecodeBridge KDecodeEnv.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Theorem named_source_to_kprime G (phi : form) N c :
  incl EqAx G -> fb N phi -> 3 < c ->
  fr c (tr source_names phi) = false ->
  (forall rho, G ⊢C dB rho (KCore 1 3 c (tr source_names phi))) ->
  G ⊢C kprime_core phi.
Proof.
  intros HE Hfb Hc Hfresh Hsource.
  unfold kprime_core, output_root. fall a. fall x.
  pose proof (Hsource (source_env var x a)) as H.
  unfold KCore in H. apply (dB_exE _ _ _ _ H). intros C.
  apply II. ctx_push HC.
  fold (private_env var x a c C) in HC.
  pose proof (dB_andE1 _ _ _ HC) as Hroot.
  pose proof (dB_andE2 _ _ _ HC) as Hclosure.
  fexists C. fsplit.
  - fintro Hphi.
    fassert Hnamed : (dB (private_env var x a c C) (tr source_names phi)).
    { apply (iff_r _ _ _ (private_env_matrix _ phi N var x a c C HE Hfb Hfresh)).
      kconv Hphi. }
    pose proof (dB_imp _ _ _ Hroot Hnamed) as Hmem.
    rewrite private_env_member in Hmem by exact Hc. exact Hmem.
  - unfold emitted_closure. simp. fall u. fintro Hu.
    pose proof (dB_allE _ _ _ u Hclosure) as HuReq.
    rewrite private_env_output in HuReq by exact Hc.
    fassert HuNamed : (dB (private_env var u a c C) (Wel 3 c)).
    { rewrite private_env_member by exact Hc. exact Hu. }
    pose proof (dB_imp _ _ _ HuReq HuNamed) as Hsome.
    apply (dB_exE _ _ _ _ Hsome). intros v. apply II. ctx_push Hv.
    rewrite private_env_input in Hv by exact Hc.
    pose proof (dB_andE1 _ _ _ Hv) as HvPhi.
    pose proof (dB_andE2 _ _ _ Hv) as HvReq.
    fexists v. fsplit.
    + pose proof (iff_l _ _ _
        (private_env_matrix _ phi N var u v c C HE Hfb Hfresh) HvPhi) as T.
      kconv T.
    + fall p. fintro Hsub.
      pose proof (dB_allE _ _ _ p HvReq) as HpReq.
      rewrite private_env_input in HpReq by exact Hc.
      fassert HsubNamed : (dB (private_env var u p c C) (KSubset 1 3 c)).
      { rewrite private_env_subset by exact Hc. kconv Hsub. }
      pose proof (dB_imp _ _ _ HpReq HsubNamed) as Hrequest.
      unfold KRequest in Hrequest. fall z. fintro Hz.
      pose proof (dB_allE _ _ _ z Hrequest) as HzReq.
      rewrite private_env_output in HzReq by exact Hc.
      fassert HzNamed : (dB (private_env var z p c C) (tr source_names phi)).
      { apply (iff_r _ _ _ (private_env_matrix _ phi N var z p c C HE Hfb Hfresh)).
        kconv Hz. }
      pose proof (dB_imp _ _ _ HzReq HzNamed) as Hfound.
      apply (dB_exE _ _ _ _ Hfound). intros y. apply II. ctx_push Hy.
      rewrite private_env_output in Hy by exact Hc.
      pose proof (dB_andE1 _ _ _ Hy) as HyPhi.
      pose proof (dB_andE2 _ _ _ Hy) as HyMem.
      fexists y. fsplit.
      * pose proof (iff_l _ _ _
          (private_env_matrix _ phi N var y p c C HE Hfb Hfresh) HyPhi) as T.
        kconv T.
      * rewrite private_env_member in HyMem by exact Hc. exact HyMem.
Qed.

Theorem decoded_source_to_kprime G (phi : form) N :
  incl EqAx G -> fb N phi ->
  (forall rho, G ⊢C dB rho (D (gated230 1 3 (ordinary_code230 phi)))) ->
  G ⊢C kprime_core phi.
Proof.
  intros HE Hfb Hsource. apply (named_source_to_kprime G phi N (ordinary_code230 phi));
    try assumption.
  - unfold ordinary_code230. apply padded230_gt_three.
  - apply ordinary_code230_fresh.
  - intros rho. apply (iff_l _ _ _ (ordinary_code230_nd_core G phi rho HE)).
    exact (Hsource rho).
Qed.

Definition ordinary_source230 (phi : form) : form :=
  let p := D (gated230 1 3 (ordinary_code230 phi)) in
  Lib (S (maxfr p)) p.

Theorem ordinary_source230_closed phi : closedf (ordinary_source230 phi).
Proof. unfold ordinary_source230. apply Lib_closed. lia. Qed.

Theorem ordinary_source230_to_kprime G (phi : form) N :
  incl EqAx G -> fb N phi -> G ⊢C ordinary_source230 phi ->
  G ⊢C kprime_core phi.
Proof.
  intros HE Hfb H. apply (decoded_source_to_kprime G phi N HE Hfb).
  intros rho. unfold ordinary_source230 in H.
  eapply Lib_inst; [|exact H]. lia.
Qed.
