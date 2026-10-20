(** Literal Runtime.matches preserves the same arithmetic configuration. *)
From PAModel Require Import Model TM230RuntimeWords TM230RuntimeTokens TM230RuntimeLeftNormal.
From K230 Require Runtime230Core.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith.
Unset Implicit Arguments.
Definition machine230_runtime_conf_wf(conf:Runtime230.sconf):Prop:=
 let '(_,_,ls,rs):=conf in machine230_runtime_segments_wf ls /\machine230_runtime_segments_wf rs.
Theorem machine230_runtime_view_wf M gap Box conf s:
 machine230_runtime_view M gap Box conf s ->machine230_runtime_conf_wf conf.
Proof.
 destruct conf as[[[q onleft]ls]rs]. intros[l[r[HL[HR HS]]]]. split;
 eapply machine230_runtime_flat_wf;eassumption.
Qed.
Theorem machine230_runtime_matches_sound M gap Box actual expected s:
 Runtime230.matches actual expected=true ->machine230_runtime_conf_wf expected ->
 machine230_runtime_view M gap Box actual s ->machine230_runtime_view M gap Box expected s.
Proof.
 destruct actual as[[[q onleft]ls]rs],expected as[[[q' onleft']ls']rs'].
 unfold Runtime230.matches.
 destruct(Nat.eqb q q')eqn:Eq;[apply Nat.eqb_eq in Eq;subst q'|discriminate].
 destruct(Bool.eqb onleft onleft')eqn:Eon;[apply Bool.eqb_prop in Eon;subst onleft'|discriminate].
 destruct(Runtime230.toks_eqb(Runtime230.norm rs)(Runtime230.norm rs'))eqn:Er;[|discriminate].
 intros El[HWL' HWR'][l[r[HL[HR HS]]]].
 apply Runtime230.toks_eqb_eq in Er,El.
 assert(HWL:machine230_runtime_segments_wf ls)by(eapply machine230_runtime_flat_wf;exact HL).
 assert(HWR:machine230_runtime_segments_wf rs)by(eapply machine230_runtime_flat_wf;exact HR).
 exists l,r. split.
 -apply(proj2(machine230_runtime_normL_correct M gap Box ls' l HWL')). rewrite <-El.
  exact(proj1(machine230_runtime_normL_correct M gap Box ls l HWL)HL).
 -split;[|exact HS].
  apply(proj2(machine230_runtime_norm_correct M gap Box rs' r HWR')). rewrite <-Er.
  exact(proj1(machine230_runtime_norm_correct M gap Box rs r HWR)HR).
Qed.
Print Assumptions machine230_runtime_view_wf.
Print Assumptions machine230_runtime_matches_sound.
