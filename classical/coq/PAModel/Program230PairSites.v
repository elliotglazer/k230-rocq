(** All 190 literal pair162 copies in the published p230 tree. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing Program230PathCode
 Program230Configurations Program230Histories Program230TransferProgram Program230Copy2Program
 Program230PairConstructorIteration Program230PairShape Program230PairShapeBody.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition program230_pair_node_graph P n :=
 fol p230(ENode(root p230))P=Some(ENode n) /\
 nodes p230 n=(ENode(n+1),ENode(n+4)) /\
 nodes p230(n+1)=(EDecnz 1,ENode(n+2)) /\
 nodes p230(n+2)=(EInc 7,ENode(n+3)) /\
 nodes p230(n+3)=(EInc 6,EContinue 3) /\
 nodes p230(n+4)=(EDecnz 6,ENode(n+5)) /\
 nodes p230(n+5)=(ENode(n+6),EContinue 3) /\
 nodes p230(n+6)=(EInc 7,ENode(n+7)) /\
 nodes p230(n+7)=(EDecnz 6,ENode(n+8)) /\
 nodes p230(n+8)=(EInc 1,EContinue 2).
Lemma program230_pair_node_shape P n:program230_pair_node_graph P n->program230_pair_shape P.
Proof.
 intros[H0[Hn[Ha[Hb[Hc[Hd[He[Hf[Hg Hh]]]]]]]]].
 assert(F:forall Q,fol p230(ENode(root p230))(P++Q)=fol p230(ENode n)Q).
 {intro Q;now rewrite fol_app,H0. }
 split.
 -exists(n+1),(n+2),(n+3);unfold program230_copy2_occurrence;split.
  +rewrite F;cbn[fol child];rewrite Hn;reflexivity.
  +repeat split;assumption.
 -split.
  +exists(n+7),(n+8);unfold program230_transfer_occurrence;split.
   *rewrite F;cbn[fol child];rewrite Hn;cbn[fol child snd];rewrite Hd;cbn[fol child snd];rewrite He;cbn[fol child fst];rewrite Hf;reflexivity.
   *split;assumption.
  +split.
   *rewrite F;cbn[fol child];rewrite Hn;cbn[fol child snd];rewrite Hd;reflexivity.
   *split.
    --rewrite F;cbn[fol child];rewrite Hn;cbn[fol child snd];rewrite Hd;cbn[fol child snd];rewrite He;cbn[fol child fst];rewrite Hf;reflexivity.
    --rewrite F;cbn[fol child];rewrite Hn;cbn[fol child snd];rewrite Hd;cbn[fol child snd];rewrite He;reflexivity.
Qed.
Definition p230_pair_site_rows:list(list bool*nat):=[
 ([true;true;true;false;true;false;false;true;false;false;true;false;false;false;false;true;true;false],56);
 ([true;true;true;false;true;false;false;true;false;false;true;false;false;false;true;true;false;true;true;false],82);
 ([true;true;true;false;true;false;false;true;false;false;true;false;false;true;false;true;false],112);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;false;true;false;false;false;false;true;true;false],154);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;false;true;false;false;true;true;true;false],178);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;false;true;false;true;true;true;false],215);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;false;true;true;false;false;true;true;false],238);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;false;true;true;true;true;false],267);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;false;false;false;false;true;true;false],292);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;false;false;true;false;true;true;false],317);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;false;true;true;false],346);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;false;false;false;false;true;true;false],371);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;false;false;true;false;true;true;false],396);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;false;true;false;true;false],426);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;false;true;true;true;false],452);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;false;true;false],479);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;false;false;false;true;true;false],503);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;false;true;false;false;true;true;false],529);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;false;true;true;false;true;false],559);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;true;true;false;false;false;false;true;true;false],586);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;true;true;false;false;true;true;true;false],610);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;true;true;true;false;true;false],640);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;false;false;false;false;true;true;false],670);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;false;false;false;true;true;false;true;true;false],696);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;false;false;true;false;true;false],726);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;true;false;false;true;false],755);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;true;false;true;true;false],781);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;true;true;false;true;true;false],803);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;false;false;false;false;true;true;false],831);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;false;false;true;false;true;true;false],856);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;false;true;false;true;false],886);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;true;false;false;false;false;true;true;false],912);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;true;false;false;true;true;false],935);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;true;false;true;false;false;true;false],963);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;true;false;true;true;false;false;true;true;false],987);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;true;false;true;true;true;true;false],1010);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;true;true;false;true;true;false],1032);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;false;true;false],1064);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;false;false;false;true;true;false],1088);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;false;true;false;false;true;true;false],1114);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;false;true;true;false;true;false],1144);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;true;true;false;false;false;false;true;true;false],1171);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;true;true;false;false;true;true;true;false],1195);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;true;true;true;false;true;false],1225);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;false;false;false;true;true;false],1250);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;false;false;true;true;false;true;true;false],1276);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;false;true;false;true;false],1306);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;true;false;false;false;true;false],1335);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;true;false;false;true;true;false],1361);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;true;false;true;false;true;true;false],1383);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;true;true;false;false;true;true;false],1409);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;true;true;true;false;true;true;false],1434);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;false;false;false;true;false],1466);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;false;true;true;false],1493);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;false;false;true;true;false],1520);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;false;false;false;false;true;true;false],1548);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;false;false;true;false;true;true;false],1573);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;false;true;false;true;false],1603);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;true;false;false;false;true;false],1633);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;true;false;true;true;false],1660);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;true;true;false;false;false;true;true;false],1684);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;true;true;false;false;true;true;false;true;true;false],1710);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;true;true;false;true;false;true;false],1740);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;false;false;false;true;true;false],1766);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;false;true;false;false;true;true;false],1792);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;false;true;true;false;true;false],1822);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;true;false;false;false;false;true;true;false],1847);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;true;false;false;true;true;true;false],1871);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;true;true;false;true;false],1901);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;true;false;false;false;true;false],1930);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;true;false;false;true;true;false],1956);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;true;false;true;false;true;true;false],1978);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;true;true;false;false;true;true;false],2004);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;true;true;true;false;true;true;false],2029);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;true;false;true;false],2059);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;true;true;false;true;false],2086);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;false;false;false;true;true;false],2112);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;false;false;true;true;false;true;true;false],2138);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;false;true;false;true;false],2168);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;false;false;false;false;true;true;false],2194);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;false;false;true;false;true;true;false],2219);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;false;true;false;true;false],2249);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;true;false;false;true;false],2278);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;true;false;true;true;false],2304);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;true;true;false;true;true;false],2326);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;false;false;false;false;true;true;false],2354);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;false;false;false;true;true;false;true;true;false],2380);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;false;false;true;false;true;false],2410);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;true;false;false;false;false;true;true;false],2436);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;true;false;false;true;true;false],2459);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;true;false;true;false;false;true;false],2487);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;true;false;true;true;false;false;true;true;false],2511);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;true;false;true;true;true;true;false],2534);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;true;true;false;true;true;false],2556);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;false;false;false;true;true;false],2584);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;false;true;false;false;false;true;true;false],2611);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;false;true;false;true;false;true;true;false],2636);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;false;true;true;false;true;false],2666);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;false;true;false],2695);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;false;false;false;true;true;false],2719);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;false;true;false;false;false;true;true;false],2746);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;false;true;false;true;false;true;true;false],2771);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;false;true;true;false;true;false],2801);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;true;false;false;true;true;false],2824);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;true;true;false;true;true;false],2849);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;false;false;false;true;true;false],2877);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;false;true;false;true;true;false],2902);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;false;false;false;true;true;false],2929);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;false;true;false;false;true;true;false],2955);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;false;true;true;false;true;false],2985);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;true;false;false;false;false;true;true;false],3010);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;true;false;false;true;true;true;false],3034);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;true;true;false;true;false],3064);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;false;false;true;false],3093);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;false;true;false;true;false],3120);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;false;false;false;false;true;true;false],3146);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;false;false;true;false;true;true;false],3171);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;false;true;false;false;true;true;false],3197);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;false;true;true;false;true;true;false],3222);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;true;false;false;false;true;true;false],3249);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;true;false;true;false;true;true;false],3274);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;true;true;false;true;false],3304);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;false;false;false;false;true;true;false],3329);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;false;false;true;true;false],3352);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;false;true;false;true;false],3379);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;false;true;true;false;false;true;true;false],3402);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;false;true;true;true;true;false],3425);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;true;false;false;false;true;true;false],3449);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;true;false;true;true;false],3472);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;true;true;false;false;true;false],3500);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;true;true;true;false;false;true;true;false],3524);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;true;true;true;true;true;false],3547);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;false;false;true;false],3575);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;false;true;false;true;false],3602);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;false;false;true;false],3632);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;false;true;false;true;false],3659);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;false;false;false;false;true;true;false],3685);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;false;false;true;true;false],3708);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;false;true;false;true;false],3735);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;false;true;true;false;false;true;true;false],3758);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;false;true;true;true;true;false],3781);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;true;false;false;false;true;true;false],3805);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;true;false;true;true;false],3828);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;true;true;false;false;true;false],3856);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;true;true;true;false;false;true;true;false],3880);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;true;true;true;true;true;false],3903);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;false;false;true;false],3931);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;false;true;false;true;false],3958);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;false;false;false;false;true;true;false],3984);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;false;false;true;true;false],4007);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;false;true;false;true;false],4034);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;false;true;true;false;false;true;true;false],4057);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;false;true;true;true;true;false],4080);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;true;false;false;false;true;true;false],4104);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;true;false;true;true;false],4127);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;true;true;false;false;true;false],4155);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;true;true;true;false;false;true;true;false],4179);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;true;true;true;true;true;false],4202);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;false;false;false;true;true;false],4227);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;false;false;true;true;false;true;true;false],4253);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;false;true;false;true;false],4283);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;false;false;true;true;false],4306);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;false;false;false;true;true;false],4333);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;false;false;true;true;false;true;true;false],4359);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;false;true;false;true;false],4389);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;true;false;false;false;true;false],4418);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;true;false;true;true;false],4445);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;true;true;false;false;false;true;true;false],4469);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;true;true;false;false;true;true;false;true;true;false],4495);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;true;true;false;true;false;true;false],4525);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;false;false;false;true;true;false],4551);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;false;true;false;false;false;true;true;false],4578);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;false;true;false;false;true;true;false;true;true;false],4604);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;false;true;false;true;false;true;false],4634);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;false;false;false;true;false],4664);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;false;true;true;false],4691);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;false;false;false;false;true;true;false],4716);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;false;false;true;true;false],4739);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;false;true;false;true;false],4766);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;false;true;true;false;false;true;true;false],4789);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;false;true;true;true;true;false],4812);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;true;false;false;false;false;true;true;false],4837);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;true;false;false;true;true;false],4860);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;true;false;true;false;true;false],4887);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;true;false;true;true;false;false;true;true;false],4910);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;true;false;true;true;true;true;false],4933);
 ([true;true;true;false;true;false;true;false;true;true;false],5015);
 ([true;true;true;true;false;false;false;false;true;true;false],5043);
 ([true;true;true;true;false;false;true;true;false],5072);
 ([true;true;true;true;true;true;false;true;true;false],5107)].

Lemma p230_pair_site_count:length p230_pair_site_rows=190.
Proof. reflexivity. Qed.
Lemma p230_pair_site_rows_correct:
 Forall(fun row=>program230_pair_node_graph(fst row)(snd row))p230_pair_site_rows.
Proof. unfold p230_pair_site_rows;repeat (apply Forall_cons;[vm_compute;repeat constructor|]);constructor. Qed.
Definition p230_pair_site P:=exists n,In(P,n)p230_pair_site_rows.
Lemma p230_pair_site_shape P:p230_pair_site P->program230_pair_shape P.
Proof.
 intros[n H];apply(program230_pair_node_shape P n).
 exact(proj1(Forall_forall _ _)p230_pair_site_rows_correct(P,n)H).
Qed.
Theorem p230_pair_site_history M P base x y z value:
 p230_pair_site P->pair_graph M x y value->exists u v time,
 program230_program_history M p230 u v time
 (program230_pair_state base(program230_path_value M P)x y z) /\
 program230_state_at M u v time
 (program230_pair_state base(program230_path_value M((inc_path P)++[false]))(zeroM M)(zeroM M)(addM M z value)) /\
 coding_lt M(zeroM M)time.
Proof.
 intros HS HP;exact(program230_pair_shape_history M P(p230_pair_site_shape P HS)base x y z value HP).
Qed.
Print Assumptions p230_pair_site_rows_correct.
Print Assumptions p230_pair_site_history.
