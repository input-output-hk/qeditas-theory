(** Copyright (c) 2015 Bill White **)
(** Distributed under the MIT/X11 software license **)
(** See http://www.opensource.org/licenses/mit-license.php **)

(** Blocks: Blocks are given by headers and deltas. The type BlockHeader of block headers
    depends on the previous block hash (with None for the genesis block), the hashroot of the
    previous ctree representing the ledger before processing the block and
    some target info. We define types of block chains and block header chains,
    leaving the reward function, how 'hits' are checked and how targets are calculated as parameters.
    The block contains a ctree corresponding to sufficient information about the previous ledger
    to process the block (ctree_of_Block) obtained by grafting the information in the block delta
    to the information in the block header. All the transactions in the block (including the
    coinstake in the header) can be combined to give one large transaction (tx_of_Block).
    If the block is valid (valid_Block), then the combined transaction will be valid and supported.
    If we start from a valid genesis ledger and a block chain is built from valid blocks (valid_BlockChain),
    then we are guaranteed that the ending ledger is also valid (endlederroot_valid).
    Furthermore, we know precisely how many currency units are in the ledger as of
    a certain block height (endledgerroot_plr_sum_correct).
 **)

Require Export CTreeGrafting.

(*** Idea: keep up with how fast the past N blocks and use this to determine the current target. I'll use 6 blocks just as a concrete option here. ***)
Definition targetinfo : Type := prod nat (list nat).
Definition nexttargetinfo (ti : targetinfo) (tm : nat) : targetinfo :=
match ti with
| (prevtm,nil) => (tm,(tm - prevtm)::nil)
| (prevtm,c1::nil) => (tm,c1::(tm - prevtm)::nil)
| (prevtm,c2::c1::nil) => (tm,c2::c1::(tm - prevtm)::nil)
| (prevtm,c3::c2::c1::nil) => (tm,c3::c2::c1::(tm - prevtm)::nil)
| (prevtm,c4::c3::c2::c1::nil) => (tm,c4::c3::c2::c1::(tm - prevtm)::nil)
| (prevtm,c5::c4::c3::c2::c1::nil) => (tm,c5::c4::c3::c2::c1::(tm - prevtm)::nil)
| (prevtm,c6::c5::c4::c3::c2::c1::_) => (tm,c5::c4::c3::c2::c1::(tm - prevtm)::nil)
end.

Definition targetinfo_timestamp (ti:targetinfo) : nat := fst ti.

Record BlockHeader {prevblockhash : option hashval} {prevledgerroot : hashval} {ti:targetinfo} : Type :=
  mkBlockHeader
    {
      newledgerroot : hashval;
      timestamp : nat;
      stake : nat;
      stakeaddr : addr;
      stakeassetid : hashval;
      totalfees : nat; (*** recall that the reward may depend on the fees in the block delta ***)
      stakeoutput : list addr_preasset;
      blocksignat : signat;
      prevledger : ctree 162
    }.
  
Record BlockDelta : Type :=
  mkBlockDelta
    {
      prevledgergraft : cgraft;
      blockdelta_stxl : list sTx
    }.

Definition Block {prevblockhash : option hashval} {prevledgerroot:hashval} {ti} : Type :=
  prod (@BlockHeader prevblockhash prevledgerroot ti) BlockDelta.

Definition coinstake {pbh plr ti} (bh:@BlockHeader pbh plr ti) : Tx :=
  ((stakeaddr bh,stakeassetid bh)::nil,stakeoutput bh).

Definition hitfun : Type  := option hashval -> nat -> nat -> nat -> addr -> Prop.

Definition targetfun : Type := targetinfo -> nat.

Definition hash_BlockHeader {pbh plr ti} (bh:@BlockHeader pbh plr ti) : hashval :=
hashopair2 pbh (hashlist (newledgerroot bh::hashnat (timestamp bh)::hashtx (coinstake bh)::nil)).

(*** A currency asset can be used to stake as long as it will not mature in the next 1000 blocks. (1000 is arbitrary, of course.) ***)
Definition not_close_to_mature : nat := 1000.

(*** The output from staking cannot be spent until 1000 blocks later. Again, 1000 is arbitrary here. ***)
Definition maturation_post_staking : nat := 1000.

Definition valid_BlockHeader (blockheight:nat) (rew:nat) (check_hit : hitfun) (targetf : targetfun) {pbh plr ti} (bh:@BlockHeader pbh plr ti) : Prop :=
  timestamp bh > targetinfo_timestamp ti
  /\
  check_signat (hash_BlockHeader bh) (blocksignat bh) (stakeaddr bh)
  /\
  check_hit pbh (timestamp bh) (targetf ti) (stake bh) (stakeaddr bh)
  /\
  ctree_hashroot (prevledger bh) = plr
  /\
  (exists a n,
     ctree_supports_asset (stakeassetid bh,(Some(a,n),currency (stake bh))) (prevledger bh) (stakeaddr bh)
     /\
     n > blockheight + not_close_to_mature)
  /\
  (*** The stake outputs must be valid. ***)
  tx_outputs_valid blockheight (stakeoutput bh)
  /\
  (*** The stake outputs must explicitly say that they cannot be spent until at least blockheight + maturation_post_staking. ***)
  (forall alpha obl u, In (alpha,(obl,u)) (stakeoutput bh) -> exists a n, obl = Some(a,n) /\ n > blockheight + maturation_post_staking)
  /\
  (*** The ctree of the previous ledger supports the declared coinstake tx. ***)
  ctree_supports_tx (coinstake bh) (prevledger bh) 0 (rew + totalfees bh).

Fixpoint sTxs_allinputs (stxl : list sTx) : list addr_assetid :=
  match stxl with
    | ((inpl,_),s)::stxr => inpl ++ sTxs_allinputs stxr
    | nil => nil
  end.

Fixpoint sTxs_alloutputs (stxl : list sTx) : list addr_preasset :=
  match stxl with
    | ((_,outpl),s)::stxr => outpl ++ sTxs_alloutputs stxr
    | nil => nil
  end.

Lemma sTxs_allinputs_iff stxl alpha h :
  In (alpha,h) (sTxs_allinputs stxl) <-> exists tx, In_dom tx stxl /\ In (alpha,h) (tx_inputs tx).
induction stxl as [|[[inpl outpl] s] stxr IH]; split.
- simpl. tauto.
- intros [tx [H1 _]]. contradiction H1.
- simpl. intros H1. apply in_app_or in H1. destruct H1 as [H1|H1].
  + exists (inpl,outpl). simpl. tauto.
  + apply IH in H1. destruct H1 as [tx H2]. exists tx. tauto.
- intros [tx [[H1|H1] H2]].
  + simpl. apply in_or_app. left. rewrite H1 in H2. exact H2.
  + simpl. apply in_or_app. right. apply IH. exists tx. tauto.
Qed.

Lemma sTxs_alloutputs_iff stxl alpha u :
  In (alpha,u) (sTxs_alloutputs stxl) <-> exists tx, In_dom tx stxl /\ In (alpha,u) (tx_outputs tx).
induction stxl as [|[[inpl outpl] s] stxr IH]; split.
- simpl. tauto.
- intros [tx [H1 _]]. contradiction H1.
- simpl. intros H1. apply in_app_or in H1. destruct H1 as [H1|H1].
  + exists (inpl,outpl). simpl. tauto.
  + apply IH in H1. destruct H1 as [tx H2]. exists tx. tauto.
- intros [tx [[H1|H1] H2]].
  + simpl. apply in_or_app. left. rewrite H1 in H2. exact H2.
  + simpl. apply in_or_app. right. apply IH. exists tx. tauto.
Qed.

Definition ctree_of_Header {pbh plr ti} (b:@Block pbh plr ti) : ctree 162 :=
  let (bh,bd) := b in
  prevledger bh.

Definition ctree_of_Block {pbh plr ti} (b:@Block pbh plr ti) : ctree 162 :=
  let (bh,bd) := b in
  ctree_cgraft (prevledgergraft bd) (prevledger bh).

Definition timestamp_of_Block {pbh plr ti} (b:@Block pbh plr ti) : nat :=
  let (bh,bd) := b in
  timestamp bh.

(*** One Tx combining all the Txs in the block, including the coinstake. ***)
Definition tx_of_Block {pbh plr ti} (b:@Block pbh plr ti) : Tx :=
  let (bh,bd) := b in
  ((stakeaddr bh,stakeassetid bh)::sTxs_allinputs (blockdelta_stxl bd),stakeoutput bh ++ sTxs_alloutputs (blockdelta_stxl bd)).

Definition valid_Block (blockheight:nat) (rew:nat) (check_hit : hitfun) (targetf : targetfun) {pbh plr ti} (b:@Block pbh plr ti) : Prop :=
  let (bh,bd) := b in
  (*** The header is valid. ***)
  valid_BlockHeader blockheight rew check_hit targetf bh
  /\
  (*** There are no duplicate transactions. ***)
  no_dups (blockdelta_stxl bd)
  /\
  (*** Each transaction in the delta has supported elaborated assets and is appropriately signed. ***)
  (forall tx sl, In (tx,sl) (blockdelta_stxl bd) ->
                 exists einpl:list asset,
                   (forall alpha a, In a einpl -> ctree_supports_asset a (ctree_of_Block (bh,bd)) alpha)
                   /\
                   tx_signatures_valid blockheight einpl (tx,sl))
  /\
  (*** Each transaction in the delta is valid at this block height. ***)
  (forall stx, In stx (blockdelta_stxl bd) -> tx_valid blockheight (fst stx))
  /\
  (*** No transaction has the stake asset as an input. ***)
  (forall tx, In_dom tx (blockdelta_stxl bd) -> ~ In (stakeaddr bh,stakeassetid bh) (tx_inputs tx))
  /\
  (*** No distinct transactions try to spend the same asset. ***)
  (forall tx1 sl1 tx2 sl2 alpha h,
     In (tx1,sl1) (blockdelta_stxl bd) ->
     In (tx2,sl2) (blockdelta_stxl bd) ->
     In (alpha,h) (tx_inputs tx1) ->
     In (alpha,h) (tx_inputs tx2) ->
     tx1 = tx2 /\ sl1 = sl2)
  /\
  (*** Ownership is not created for the same address alpha by the coinstake and a tx in the block. ***)
  (forall tx sl alpha b beta obl u beta' obl' u',
     In (tx,sl) (blockdelta_stxl bd) ->
     In (alpha,(obl,owns b beta u)) (stakeoutput bh) ->
     ~In (alpha,(obl',owns b beta' u')) (tx_outputs tx))
  /\
  (*** Ownership is not created for the same address alpha by two txs in the block. ***)
  (forall tx1 sl1 tx2 sl2 alpha b beta obl u beta' obl' u',
     In (tx1,sl1) (blockdelta_stxl bd) ->
     In (tx2,sl2) (blockdelta_stxl bd) ->
     In (alpha,(obl,owns b beta u)) (tx_outputs tx1) ->
     In (alpha,(obl',owns b beta' u')) (tx_outputs tx2) ->
     tx1 = tx2 /\ sl1 = sl2)
  /\
  (*** The cgraft is valid. ***)
  cgraft_valid (prevledgergraft bd)
  /\
  (*** Every transaction is supported by the grafted ctree with 0 reward. ***)
  (forall tx, In_dom tx (blockdelta_stxl bd)
              -> exists fee, ctree_supports_tx tx (ctree_of_Block (bh,bd)) fee 0)
  (*** The total inputs and outputs match up with the declared fee. ***)
  /\
  (exists utot:nat,
     ctree_asset_value_in (ctree_of_Block (bh,bd)) (sTxs_allinputs (blockdelta_stxl bd)) utot
     /\
     asset_value_out (sTxs_alloutputs (blockdelta_stxl bd)) + (totalfees bh) = utot)
  /\
  exists T:ctree 162,
    ctree_hashroot T = newledgerroot bh
    /\ tx_octree_trans (tx_of_Block (bh,bd)) (Some (ctree_of_Block (bh,bd))) = Some T.

Inductive BlockChain {genesisledgerroot:hashval} : hashval -> hashval -> targetinfo -> nat -> Type :=
| BlockChainGen {genti} (b : @Block None genesisledgerroot genti) : BlockChain (hash_BlockHeader (fst b)) (newledgerroot (fst b)) (nexttargetinfo genti (timestamp_of_Block b)) 0
| BlockChainSucc pbh plr ti n : BlockChain pbh plr ti n -> forall b:@Block (Some pbh) plr ti, BlockChain (hash_BlockHeader (fst b)) (newledgerroot (fst b)) (nexttargetinfo ti (timestamp_of_Block b)) (S n).

Inductive BlockHeaderChain {genesisledgerroot:hashval} : hashval -> hashval -> targetinfo -> nat -> Type :=
| BlockHeaderChainGen {genti} (bh : @BlockHeader None genesisledgerroot genti) : BlockHeaderChain (hash_BlockHeader bh) (newledgerroot bh) (nexttargetinfo genti (timestamp bh))  0
| BlockHeaderChainSucc pbh plr ti n : BlockHeaderChain pbh plr ti n -> forall bh:@BlockHeader (Some pbh) plr ti, BlockHeaderChain (hash_BlockHeader bh) (newledgerroot bh) (nexttargetinfo ti (timestamp bh)) (S n).

Fixpoint BlockChain_headers {genlr pbh plr ti n} (bc : @BlockChain genlr pbh plr ti n) : BlockHeaderChain pbh plr ti n :=
match bc with
| BlockChainGen genti (bh,_) => BlockHeaderChainGen bh
| BlockChainSucc pbh plr ti n bc (bh,_) => BlockHeaderChainSucc pbh plr ti n (BlockChain_headers bc) bh
end.

Fixpoint valid_BlockChain (rewfn:nat -> nat) (check_hit:hitfun) (targetf:targetfun) {genlr pbh plr ti n} (bc : @BlockChain genlr pbh plr ti n) : Prop :=
match bc with
| BlockChainGen genti b => valid_Block 0 (rewfn 0) check_hit targetf b
| BlockChainSucc pbh plr ti n bc b => valid_BlockChain rewfn check_hit targetf bc /\ valid_Block (S n) (rewfn (S n)) check_hit targetf b
end.

Fixpoint valid_BlockHeaderChain (rewfn:nat -> nat) (check_hit:hitfun) (targetf:targetfun) {genlr pbh plr ti n} (bc : @BlockHeaderChain genlr pbh plr ti n) : Prop :=
match bc with
| BlockHeaderChainGen genti bh => valid_BlockHeader 0 (rewfn 0) check_hit targetf bh
| BlockHeaderChainSucc pbh plr ti n bc bh => valid_BlockHeaderChain rewfn check_hit targetf bc /\ valid_BlockHeader (S n) (rewfn (S n)) check_hit targetf bh
end.

Lemma tx_of_Block_valid blockheight rew check_hit targetf {pbh plr ti} (b:@Block pbh plr ti) :
  valid_Block blockheight rew check_hit targetf b ->
  tx_valid blockheight (tx_of_Block b).
destruct b as [bh bd].
intros HvB. generalize HvB.
intros [[HvBaa [HvBab [HvBac [HvBad [HvBae [HvBaf [HvBag HvBah]]]]]]] [HvBb [HvBc [HvBd [HvBe [HvBf [HvBg [HvBh [HvBi [HvBj [HvBk HvBl]]]]]]]]]]].
split.
- split.
  + simpl. discriminate.
  + simpl. apply no_dups_cons.
    * intros H1. apply sTxs_allinputs_iff in H1.
      destruct H1 as [[inpl outpl] [H2 H3]].
      revert H2 H3. apply HvBe.
    * { revert HvBb HvBd HvBf. unfold sTxs_allinputs. generalize (blockdelta_stxl bd).
        clear.
        (*** This could be made into a reasonable lemma instead of giving a double induction in a subproof. ***)
        induction l as [|[[inpl outpl] sl] txl IH].
        - simpl. intros H0 H1 H2. apply no_dups_nil.
        - simpl. intros H0 H1 H2. apply no_dups_app.
          + assert (L1: (inpl, outpl, sl) = (inpl, outpl, sl) \/ In (inpl, outpl, sl) txl) by now left.
            destruct (H1 ((inpl,outpl),sl) L1) as [[_ H1b] _].
            exact H1b.
          + apply IH.
            * inversion H0. assumption.
            * intros stx H3. apply H1. now right.
            * intros tx1 sl1 tx2 sl2 alpha h H3 H4. apply H2; now right.
          + revert H0 H2. clear.
            induction txl as [|[[inpl2 outpl2] sl2] txr IH]; intros H0 H2 [alpha h] H3.
            * simpl. tauto.
            * { intros H4. apply in_app_or in H4.
                destruct H4 as [H4|H4].
                - inversion H0. apply H5. left.
                  assert (L1: (inpl,outpl) = (inpl2,outpl2) /\ sl = sl2).
                  { apply (H2 (inpl,outpl) sl (inpl2,outpl2) sl2 alpha h).
                    - now left.
                    - right. now left.
                    - exact H3.
                    - exact H4.
                  }
                  destruct L1 as [L1a L1b].
                  rewrite L1a. rewrite L1b.
                  reflexivity.
                - revert H4. apply IH.
                  + inversion H0. apply no_dups_cons.
                    * intros H6. apply H4. now right.
                    * inversion H5. assumption.
                  + intros tx3 sl3 tx4 sl4 beta k H6 H7. apply H2.
                    * simpl. tauto.
                    * simpl. tauto.
                  + exact H3.
              }
      }
- split.
  + intros alpha i obl beta u i' obl' beta' u' b H1 H2.
    simpl in H1. simpl in H2.
    apply nth_error_app in H1. destruct H1 as [H1|[j [H1a H1b]]].
    * { apply nth_error_app in H2. destruct H2 as [H2|[j' [H2a H2b]]].
        - destruct HvBaf as [H3 _].
          revert H1 H2. apply H3.
        - exfalso.
          apply nth_error_In in H1.
          apply nth_error_In in H2b.
          apply sTxs_alloutputs_iff in H2b.
          destruct H2b as [tx' [H3 H4]].
          apply In_In_dom_lem in H3.
          destruct H3 as [sl' H3].
          revert H3 H1 H4. apply HvBg.
      }
    * { apply nth_error_app in H2. destruct H2 as [H2|[j' [H2a H2b]]].
        - exfalso.
          apply nth_error_In in H2.
          apply nth_error_In in H1b.
          apply sTxs_alloutputs_iff in H1b.
          destruct H1b as [tx' [H3 H4]].
          apply In_In_dom_lem in H3.
          destruct H3 as [sl' H3].
          revert H3 H2 H4. apply HvBg.
        - assert (L1: j = j' /\ obl = obl' /\ beta = beta' /\ u = u').
          { revert HvBb HvBd HvBh H1b H2b. generalize (blockdelta_stxl bd) as stxl.
            intros stxl. clear. revert j j'.
            induction stxl as [|[[inpl outpl] sl] stxr IH].
            - simpl. intros [|j] j' H0 H1 H2 H3 H4; discriminate H3.
            - simpl. intros j j' H0 H1 H2 H3 H4.
              apply nth_error_app in H3; destruct H3 as [H3|[k [H3a H3b]]];
              apply nth_error_app in H4; destruct H4 as [H4|[k' [H4a H4b]]].
              + assert (L1a: (inpl, outpl, sl) = ((inpl,outpl),sl) \/ In ((inpl,outpl),sl) stxr) by now left.
                destruct (H1 ((inpl,outpl),sl) L1a) as [_ [H1c _]].
                apply (H1c alpha j obl beta u j' obl' beta' u' b).
                * exact H3.
                * exact H4.
              + exfalso.
                apply nth_error_In in H3.
                apply nth_error_In in H4b.
                apply sTxs_alloutputs_iff in H4b.
                destruct H4b as [tx' [H5 H6]].
                apply In_In_dom_lem in H5.
                destruct H5 as [sl' H5].
                assert (L2: (inpl, outpl) = tx' /\ sl = sl').
                { apply (H2 (inpl,outpl) sl tx' sl' alpha b beta obl u beta' obl' u').
                  - now left.
                  - now right.
                  - exact H3.
                  - exact H6.
                }
                destruct L2 as [L2a L2b].
                inversion H0.
                apply H7.
                rewrite L2a. rewrite L2b. exact H5.
              + exfalso.
                apply nth_error_In in H4.
                apply nth_error_In in H3b.
                apply sTxs_alloutputs_iff in H3b.
                destruct H3b as [tx' [H5 H6]].
                apply In_In_dom_lem in H5.
                destruct H5 as [sl' H5].
                assert (L2: (inpl, outpl) = tx' /\ sl = sl').
                { apply (H2 (inpl,outpl) sl tx' sl' alpha b beta' obl' u' beta obl u).
                  - now left.
                  - now right.
                  - exact H4.
                  - exact H6.
                }
                destruct L2 as [L2a L2b].
                inversion H0.
                apply H7.
                rewrite L2a. rewrite L2b. exact H5.
              + assert (L1a: k = k' /\ obl = obl' /\ beta = beta' /\ u = u').
                { apply IH.
                  - inversion H0. assumption.
                  - intros stx H5. apply H1. now right.
                  - intros tx1 sl1 tx2 sl2 gamma c delta1 obl1 v1 delta2 obl2 v2 H5 H6.
                    apply (H2 tx1 sl1 tx2 sl2 gamma c delta1 obl1 v1 delta2 obl2 v2).
                    + now right.
                    + now right.
                  - exact H3b.
                  - exact H4b.
                }
                destruct L1a as [L1aa L1ab]. split.
                * congruence.
                * exact L1ab.
          }
          destruct L1 as [L1a L1b]. split.
          + congruence.
          + exact L1b.
      }
  + intros alpha a b beta H1.
    simpl in H1. apply in_app_or in H1.
    destruct H1 as [H1|H1].
    * destruct HvBaf as [_ HvBaf2].
      revert H1. apply HvBaf2.
    * apply sTxs_alloutputs_iff in H1. destruct H1 as [[inpl outpl] [H2 H3]].
      apply In_In_dom_lem in H2.
      destruct H2 as [sl H2].
      destruct (HvBd ((inpl,outpl),sl) H2) as [_ [_ H4]].
      revert H3. apply H4.
Qed.

Lemma tx_of_Block_input_iff alpha h {pbh plr ti} (b : @Block pbh plr ti) :
  In (alpha,h) (tx_inputs (tx_of_Block b))
  <->
  ((alpha = stakeaddr (fst b) /\ h = stakeassetid (fst b))
   \/
   exists tx sl, In (tx,sl) (blockdelta_stxl (snd b)) /\ In (alpha,h) (tx_inputs tx)).
destruct b as [bh bd]. simpl. split; intros [H1|H1].
- left. inversion H1. tauto.
- right. apply sTxs_allinputs_iff in H1.
  destruct H1 as [tx [H1 H2]]. apply In_In_dom_lem in H1.
  destruct H1 as [sl H1]. exists tx. exists sl. tauto.
- left. destruct H1 as [H2 H3]. congruence.
- right. apply sTxs_allinputs_iff. destruct H1 as [tx [sl [H1 H2]]].
  exists tx. split.
  + revert H1. apply In_In_dom_lem_2.
  + exact H2.
Qed.

Lemma tx_of_Block_output_iff alpha oblu {pbh plr ti} (b : @Block pbh plr ti) :
 In (alpha, oblu) (tx_outputs (tx_of_Block b))
 <->
 (In (alpha, oblu) (stakeoutput (fst b))
  \/
   exists tx sl, In (tx,sl) (blockdelta_stxl (snd b)) /\ In (alpha,oblu) (tx_outputs tx)).
destruct b as [bh bd]. simpl. split; intros H1.
- apply in_app_or in H1. destruct H1 as [H1|H1].
  + now left.
  + right. apply sTxs_alloutputs_iff in H1.
    destruct H1 as [tx [H1 H2]]. apply In_In_dom_lem in H1.
    destruct H1 as [sl H1]. exists tx. exists sl. tauto.
- apply in_or_app. destruct H1 as [H1|H1].
  + now left.
  + right. apply sTxs_alloutputs_iff. destruct H1 as [tx [sl [H1 H2]]].
    exists tx. split.
    * revert H1. apply In_In_dom_lem_2.
    * exact H2.
Qed.

Lemma tx_of_Block_output_uses_iff alpha c {pbh plr ti} (b : @Block pbh plr ti) :
 In alpha (output_uses c (tx_outputs (tx_of_Block b)))
 <->
 (In alpha (output_uses c (stakeoutput (fst b)))
  \/
   exists tx sl, In (tx,sl) (blockdelta_stxl (snd b)) /\ In alpha (output_uses c (tx_outputs tx))).
destruct b as [bh bd].
assert (L1: In alpha (output_uses c (sTxs_alloutputs (blockdelta_stxl bd)))
            <->
            exists (tx : Tx) (sl : list gensignat),
              In (tx, sl) (blockdelta_stxl bd) /\
              In alpha (output_uses c (tx_outputs tx))).
{ generalize (blockdelta_stxl bd) as stxl.
  induction stxl as [|[[inpl outpl] sl] stxl IH].
  - simpl. split.
    + tauto.
    + intros [tx [sl [[] _]]].
  - simpl. split.
    + intros H1. apply output_uses_app_or in H1. destruct H1 as [H1|H1].
      * exists (inpl,outpl). exists sl. simpl. tauto.
      * apply IH in H1. destruct H1 as [tx [sl' [H2 H3]]].
        exists tx. exists sl'. tauto.
    + intros [tx [sl' [[H1|H1] H2]]].
      * apply output_uses_app_or. left. inversion H1.
        subst tx. exact H2.
      * apply output_uses_app_or. right. apply IH.
        exists tx. exists sl'. tauto.
}
simpl. split.
- intros H1. apply output_uses_app_or in H1. destruct H1 as [H1|H1].
  + now left.
  + right. now apply L1.
- intros [H1|H1].
  + apply output_uses_app_or. now left.
  + apply output_uses_app_or. right. apply L1. exact H1.
Qed.

Opaque ctree_supports_addr.
Transparent output_uses.

Lemma ctree_rights_balanced_app (T:ctree 162) alpha b inpl1 outpl1 inpl2 outpl2 :
  ctree_rights_balanced T alpha b inpl1 outpl1 ->
  ctree_rights_balanced T alpha b inpl2 outpl2 ->
  ctree_rights_balanced T alpha b (inpl1 ++ inpl2) (outpl1 ++ outpl2).
unfold ctree_rights_balanced. intros H1 H2 rtot1 rtot2 h obl beta u H3 H4 H5.
rewrite output_uses_app in H3. rewrite count_rights_used_app in H3.
rewrite rights_out_app in H5.
assert (L3: exists rtot3 rtot4 : nat,
              ctree_rights_consumed b alpha T inpl1 rtot3 /\
              rtot4 * u <= units_sent_to_addr beta outpl1 /\
              count_rights_used (output_uses b outpl1) alpha +
              rights_out b outpl1 alpha = rtot3 + rtot4).
{ apply (H1 (count_rights_used (output_uses b (outpl1)) alpha) (rights_out b outpl1 alpha) h obl beta u).
    - reflexivity.
    - exact H4.
    - reflexivity.
}
assert (L4: exists rtot3 rtot4 : nat,
              ctree_rights_consumed b alpha T inpl2 rtot3 /\
              rtot4 * u <= units_sent_to_addr beta outpl2 /\
              count_rights_used (output_uses b outpl2) alpha +
              rights_out b outpl2 alpha = rtot3 + rtot4).
{ apply (H2 (count_rights_used (output_uses b (outpl2)) alpha) (rights_out b outpl2 alpha) h obl beta u).
  - reflexivity.
  - exact H4.
  - reflexivity.
}
destruct L3 as [rtot31 [rtot41 [L3a [L3b L3c]]]].
destruct L4 as [rtot32 [rtot42 [L4a [L4b L4c]]]].
exists (rtot31 + rtot32). exists (rtot41 + rtot42).
repeat split.
- now apply ctree_rights_consumed_app.
- rewrite units_sent_to_addr_app.
  rewrite mult_plus_distr_r.
  omega.
- omega.
Qed.

Transparent output_uses.

Lemma ctree_rights_balanced_sTx_all (T:ctree 162) alpha b (stxl : list sTx) :
  (forall tx, In_dom tx stxl -> ctree_rights_balanced T alpha b (tx_inputs tx) (tx_outputs tx)) ->
  ctree_rights_balanced T alpha b (sTxs_allinputs stxl) (sTxs_alloutputs stxl).
induction stxl as [|[[inpl outpl] sl] stxl IH].
- simpl. intros _ rtot1 rtot2 h obl beta u H1 H2 H3.
  exists 0. exists 0. repeat split.
  + apply ctree_rights_consumed_nil.
  + destruct b; simpl in H1; simpl in H3; omega.
  + rewrite rights_out_nil in H3.
    rewrite output_uses_nil in H1.
    rewrite count_rights_used_none in H1.
    * subst rtot1. subst rtot2. reflexivity.
    * simpl. tauto.
- intros H1. simpl. apply ctree_rights_balanced_app.
  + apply (H1 (inpl,outpl)). now left.
  + apply IH. intros tx H2. apply H1. now right.
Qed.

(*** These two lemmas were pulled out from the main proof to help Coq process the main proof. ***)
Lemma tx_of_Block_supported_lem_1 blockheight rew {pbh plr ti} (bh:@BlockHeader pbh plr ti) (bd:BlockDelta) utot :
  ctree_valid (ctree_of_Block (bh, bd)) ->
  subqc (prevledger bh) (ctree_of_Block (bh, bd)) ->
  (exists (a : addr) (n : nat),
     ctree_supports_asset
       (stakeassetid bh, (Some(a,n), currency (stake bh))) 
       (prevledger bh) (stakeaddr bh) /\
     n > blockheight + not_close_to_mature) ->
  ctree_supports_tx (coinstake bh) (prevledger bh) 0 (rew + totalfees bh) ->
  asset_value_out (sTxs_alloutputs (blockdelta_stxl bd)) + totalfees bh = utot ->
  asset_value_out (tx_outputs (tx_of_Block (bh, bd))) + 0 =
  stake bh + utot + rew.
  intros HT Lsubqc HvBae HvBah H3.
  simpl. rewrite asset_value_out_app.
  destruct HvBah as [_ [[utot2 [H4 H5]] _]].
  assert (L2: utot2 = stake bh).
  { revert HT Lsubqc HvBae H4. clear.
    intros [f [[_ [Hf2 _]] HTf]] Lsubqc.
    intros [a' [n [H4 H5]]]. simpl. intros H1. inversion H1.
    - inversion H2.
      assert (L2a : ctree_supports_asset
                      (stakeassetid bh, (Some(a',n), currency (stake bh))) 
                      (ctree_of_Block (bh,bd))
                      (stakeaddr bh)).
      { revert H4. apply subqc_supports_asset. exact Lsubqc. }
      assert (L2b : ctree_supports_asset a
                                         (ctree_of_Block (bh,bd))
                                         (stakeaddr bh)).
      { revert H6. apply subqc_supports_asset. exact Lsubqc. }
      generalize (ctree_supports_asset_In_statefun _ _ f _ HTf L2a).
      intros L2a'.
      generalize (ctree_supports_asset_In_statefun _ _ f _ HTf L2b).
      intros L2b'.
      rewrite <- H0 in L2a'.
      destruct a as [h' [obl' u']].
      simpl in H9. rewrite <- H9 in L2b'. rewrite <- H0 in L2b'.
      destruct (Hf2 h (stakeaddr bh) (Some(a',n),currency (stake bh)) (stakeaddr bh) (obl',u') L2a' L2b') as [_ H11].
      inversion H11. subst u'.
      unfold asset_value in H8. simpl in H8. inversion H8.
      inversion H3. omega.
    - exfalso.
      assert (L2a : ctree_supports_asset
                      (stakeassetid bh, (Some(a', n), currency (stake bh))) 
                      (ctree_of_Block (bh,bd))
                      (stakeaddr bh)).
      { revert H4. apply subqc_supports_asset. exact Lsubqc. }
      assert (L2b : ctree_supports_asset a
                                         (ctree_of_Block (bh,bd))
                                         (stakeaddr bh)).
      { revert H6. apply subqc_supports_asset. exact Lsubqc. }
      generalize (ctree_supports_asset_In_statefun _ _ f _ HTf L2a).
      intros L2a'.
      generalize (ctree_supports_asset_In_statefun _ _ f _ HTf L2b).
      intros L2b'.
      rewrite <- H0 in L2a'.
      destruct a as [h' [obl' u']].
      simpl in H9. rewrite <- H9 in L2b'. rewrite <- H0 in L2b'.
      destruct (Hf2 h (stakeaddr bh) (Some(a',n),currency (stake bh)) (stakeaddr bh) (obl',u') L2a' L2b') as [_ H11].
      inversion H11. subst u'.
      unfold asset_value in H8. simpl in H8. discriminate H8.
  }
  revert H3 H5 L2. clear. intros H3 H5 L2.
  simpl in H5.
  omega.
Qed.

Lemma tx_of_Block_supported_lem_2 rew {pbh plr ti} (bh:@BlockHeader pbh plr ti) (bd:BlockDelta) :
  subqc (prevledger bh) (ctree_of_Block (bh, bd)) ->
  ctree_supports_tx (coinstake bh) (prevledger bh) 0 (rew + totalfees bh) ->
  (forall tx : Tx,
     In_dom tx (blockdelta_stxl bd) ->
     exists fee : nat, ctree_supports_tx tx (ctree_of_Block (bh, bd)) fee 0) ->
  forall (obl : obligation) (nonce : nat) (d : data) (alpha : addr),
    In (alpha, (obl, publication nonce d)) (tx_outputs (tx_of_Block (bh, bd))) ->
    exists (beta : addr) (h : hashval) (obl0 : obligation),
      beta = hashval_intention_addr (hashpair (hashnat nonce) (hashdata d)) /\
      In (beta, h) (tx_inputs (tx_of_Block (bh, bd))) /\
      ctree_supports_asset (h, (obl0, intention alpha))
                           (ctree_of_Block (bh, bd)) beta.
  intros Lsubqc HvBah HvBj.
  intros obl nonce d alpha H1.
  apply tx_of_Block_output_iff in H1.
  destruct H1 as [H1|[tx' [sl' [H2 H3]]]].
  + destruct HvBah as [_ [_ [_ [H5 _]]]].
    destruct (H5 obl nonce d alpha H1) as [beta [h [obl' [H6 [H7 H8]]]]].
    exists beta. exists h. exists obl'. repeat split.
    * exact H6.
    * apply tx_of_Block_input_iff.
      left. simpl in H7. destruct H7 as [H7|[]].
      inversion H7. split; reflexivity.
    * revert H8. apply subqc_supports_asset. exact Lsubqc.
  + simpl in H2. generalize H2. intros H2a. apply In_In_dom_lem_2 in H2a.
    destruct (HvBj tx' H2a) as [fee [_ [_ [_ [H5 _]]]]].
    destruct (H5 obl nonce d alpha H3) as [beta [h [obl' [H6 [H7 H8]]]]].
    exists beta. exists h. exists obl'. repeat split.
    * exact H6.
    * apply tx_of_Block_input_iff.
      right. exists tx'. exists sl'. tauto.
    * exact H8.
Qed.

Opaque ctree_full_approx_addr.

Theorem tx_of_Block_supported blockheight rew check_hit targetf {pbh plr ti} (b:@Block pbh plr ti) :
  ctree_valid (ctree_of_Block b) ->
  valid_Block blockheight rew check_hit targetf b ->
  ctree_supports_tx (tx_of_Block b) (ctree_of_Block b) 0 rew.
destruct b as [bh bd]. intros HT HvB. generalize HvB.
intros [[HvBaa [HvBab [HvBac [HvBad [HvBae [HvBaf [HvBag HvBah]]]]]]] [HvBb [HvBc [HvBd [HvBe [HvBf [HvBg [HvBh [HvBi [HvBj [HvBk HvBl]]]]]]]]]]].
generalize HvBah. intros [HvBah1 [HvBah23 [[HvBah4a HvBah4b] [HvBah5 [HvBah6 [HvBah7 HvBah8]]]]]].
assert (Lsubqc: subqc (prevledger bh) (ctree_of_Block (bh,bd))).
{ unfold ctree_of_Block. apply ctree_cgraft_subqc. exact HvBi. }
split.
- intros alpha oblu H1.
  apply tx_of_Block_output_iff in H1.
  destruct H1 as [H1|[tx' [sl' [H2 H3]]]].
  + generalize (HvBah1 alpha oblu H1).
    apply subqc_supports_addr.
    exact Lsubqc.
  + apply In_In_dom_lem_2 in H2.
    destruct (HvBj tx' H2) as [fee [H2a _]].
    revert H3. apply H2a.
- split.
  + destruct HvBk as [utot [H2 H3]].
    exists (stake bh + utot).
    split.
    * { change (ctree_asset_value_in (ctree_of_Block (bh, bd))
                                     ((stakeaddr bh, stakeassetid bh)
                                        :: sTxs_allinputs (blockdelta_stxl bd))
                                     (stake bh + utot)).
        destruct HvBae as [a [n [H4 H5]]].
        apply ctree_asset_value_in_cons with (a := (stakeassetid bh,(Some(a,n),currency (stake bh)))).
        - exact H2.
        - revert H4. apply subqc_supports_asset. exact Lsubqc.
        - reflexivity.
        - reflexivity.
      }
    * revert HT Lsubqc HvBae HvBah H3.
      apply tx_of_Block_supported_lem_1.
  + split.
    * { split.
        - intros alpha b H1.
          destruct H1 as [H1|[beta2 [obl2 [n2 H1]]]].
          + apply tx_of_Block_output_uses_iff in H1.
            destruct H1 as [H1|[tx [sl [H1 H2]]]].
            * { assert (L3: rights_mentioned alpha b (tx_outputs (coinstake bh))).
                { now left. }
                destruct (HvBah4a alpha b L3) as [H4 [H5 H6]].
                split.
                - revert H4. apply subqc_full_approx_addr. exact Lsubqc.
                - split.
                  + intros [h' [obl' [beta' H7]]].
                    apply H5. exists h'. exists obl'. exists beta'.
                    revert H4 H7. apply subqc_full_approx_supports_asset_conv.
                    exact Lsubqc.
                  + change (ctree_rights_balanced (ctree_of_Block (bh, bd)) alpha b
                                                  (((stakeaddr bh, stakeassetid bh) ::nil) ++ sTxs_allinputs (blockdelta_stxl bd))
                                                  (stakeoutput bh ++ sTxs_alloutputs (blockdelta_stxl bd))).
                    apply ctree_rights_balanced_app.
                    * { intros rtot1 rtot2 h obl beta u H7 H8 H9.
                        assert (L8: ctree_supports_asset (h, (obl, owns b beta (Some u))) (prevledger bh) alpha).
                        { revert Lsubqc H4 H8. apply subqc_full_approx_supports_asset_conv. }
                        destruct (H6 rtot1 rtot2 h obl beta u H7 L8 H9) as [rtot3 [rtot4 [H10 [H11 H12]]]].
                        exists rtot3. exists rtot4.
                        repeat split.
                        - revert Lsubqc H10. apply subqc_rights_consumed.
                        - exact H11.
                        - exact H12.
                      }
                    * { apply ctree_rights_balanced_sTx_all.
                        intros tx H7.
                        destruct (HvBj tx H7) as [fee Hs].
                        generalize Hs. intros [_ [_ [[H8a H8b] _]]].
                        destruct (rights_mentioned_dec alpha b (tx_outputs tx)) as [D1|D1].
                        - destruct (H8a alpha b D1) as [_ [_ H9]].
                          exact H9.
                        - intros rtot1 rtot2 h obl beta u H9 H10 H11.
                          exists 0. exists 0.
                          rewrite (rights_unmentioned_no_rights_out alpha b _ D1) in H11.
                          rewrite (rights_unmentioned_no_rights_used alpha b _ D1) in H9.
                          subst rtot1. subst rtot2.
                          repeat split.
                          + apply ctree_supports_tx_can_support in Hs.
                            destruct Hs as [Hc1 _].
                            revert D1 Hc1 H8b.
                            clear.
                            intros D1.
                            generalize (tx_inputs tx) as inpl.
                            intros inpl. induction inpl as [|[gamma h] inpl IH].
                            * intros _ _. apply ctree_rights_consumed_nil.
                            * { intros Hc1 H8b.
                                assert (L9: exists oblu : obligation * preasset,
                                              ctree_supports_asset (h, oblu) (ctree_of_Block (bh, bd)) gamma).
                                { apply Hc1. now left. }
                                destruct L9 as [[obl u] L9a].
                                apply ctree_rights_consumed_skip with (obl := obl) (u := u).
                                - apply IH.
                                  + intros delta k H9. apply Hc1. now right.
                                  + intros delta c beta k obl' n H9. apply H8b. now right.
                                - exact L9a.
                                - intros [r2 H10]. subst u.
                                  apply D1. revert L9a. apply H8b.
                                  now left.
                              }
                          + omega.
                      }
              }
            * { generalize H1. intros H1a. apply In_In_dom_lem_2 in H1a.
                destruct (HvBj tx H1a) as [fee Hs].
                generalize Hs. intros [_ [_ [[H8a H8b] _]]].
                assert (L3: rights_mentioned alpha b (tx_outputs tx)).
                { left. exact H2. }
                destruct (H8a _ _ L3) as [H4 [H5 H6]].
                split.
                - exact H4.
                - split.
                  + intros [h' [obl' [beta' H7]]].
                    apply H5. exists h'. exists obl'. exists beta'.
                    exact H7.
                  + change (ctree_rights_balanced (ctree_of_Block (bh, bd)) alpha b
                                                  (((stakeaddr bh, stakeassetid bh) ::nil) ++ sTxs_allinputs (blockdelta_stxl bd))
                                                  (stakeoutput bh ++ sTxs_alloutputs (blockdelta_stxl bd))).
                    apply ctree_rights_balanced_app.
                    * { intros rtot1 rtot2 h obl beta u H7 H8 H9.
                        destruct (rights_mentioned_dec alpha b (tx_outputs (coinstake bh))) as [D1|D1].
                        - destruct (HvBah4a alpha b D1) as [H4' [H5' H6']].
                          assert (L8: ctree_supports_asset (h, (obl, owns b beta (Some u))) (prevledger bh) alpha).
                          { revert Lsubqc H4' H8. apply subqc_full_approx_supports_asset_conv. }
                          destruct (H6' rtot1 rtot2 h obl beta u H7 L8 H9) as [rtot3 [rtot4 [H10 [H11 H12]]]].
                          exists rtot3. exists rtot4.
                          repeat split.
                          + revert Lsubqc H10. apply subqc_rights_consumed.
                          + exact H11.
                          + exact H12.
                        - exists 0. exists 0.
                          assert (L9a: rights_out b (stakeoutput bh) alpha = 0).
                          { exact (rights_unmentioned_no_rights_out alpha b _ D1). }
                          rewrite L9a in H9.
                          assert (L7a: count_rights_used (output_uses b (stakeoutput bh)) alpha = 0).
                          { exact (rights_unmentioned_no_rights_used alpha b _ D1). }
                          rewrite L7a in H7.
                          subst rtot1. subst rtot2.
                          repeat split.
                          + destruct HvBae as [a' [n [H10 _]]].
                            assert (L10: ctree_supports_asset
                                           (stakeassetid bh, (Some(a', n), currency (stake bh)))
                                           (ctree_of_Block (bh,bd)) (stakeaddr bh)).
                            { revert Lsubqc H10. apply subqc_supports_asset. }
                            assert (L11: ~exists r2, currency (stake bh) = rights b r2 alpha).
                            { intros [r2 H11]. discriminate H11. }
                            revert L10 L11. apply ctree_rights_consumed_skip.
                            apply ctree_rights_consumed_nil.
                          + omega.
                      }
                    * { apply ctree_rights_balanced_sTx_all.
                        intros tx' H7.
                        destruct (HvBj tx' H7) as [fee' Hs'].
                        generalize Hs'. intros [_ [_ [[H8a' H8b'] _]]].
                        destruct (rights_mentioned_dec alpha b (tx_outputs tx')) as [D1'|D1'].
                        - destruct (H8a' alpha b D1') as [_ [_ H9]].
                          exact H9.
                        - intros rtot1 rtot2 h obl beta u H9 H10 H11.
                          exists 0. exists 0.
                          rewrite (rights_unmentioned_no_rights_out alpha b _ D1') in H11.
                          rewrite (rights_unmentioned_no_rights_used alpha b _ D1') in H9.
                          subst rtot1. subst rtot2.
                          repeat split.
                          + apply ctree_supports_tx_can_support in Hs'.
                            destruct Hs' as [Hc1' _].
                            revert D1' Hc1' H8b'.
                            clear.
                            intros D1'.
                            generalize (tx_inputs tx') as inpl.
                            intros inpl. induction inpl as [|[gamma h] inpl IH].
                            * intros _ _. apply ctree_rights_consumed_nil.
                            * { intros Hc1' H8b'.
                                assert (L9: exists oblu : obligation * preasset,
                                              ctree_supports_asset (h, oblu) (ctree_of_Block (bh, bd)) gamma).
                                { apply Hc1'. now left. }
                                destruct L9 as [[obl u] L9a].
                                apply ctree_rights_consumed_skip with (obl := obl) (u := u).
                                - apply IH.
                                  + intros delta k H9. apply Hc1'. now right.
                                  + intros delta c beta k obl' n H9. apply H8b'. now right.
                                - exact L9a.
                                - intros [r2 H10]. subst u.
                                  apply D1'. revert L9a. apply H8b'.
                                  now left.
                              }
                          + omega.
                      }
              }
          + apply tx_of_Block_output_iff in H1.
            destruct H1 as [H1|[tx [sl [H1 H2]]]].
            * { assert (L3: rights_mentioned alpha b (tx_outputs (coinstake bh))).
                { right. exists beta2. exists obl2. exists n2. exact H1. }
                destruct (HvBah4a alpha b L3) as [H4 [H5 H6]].
                split.
                - revert H4. apply subqc_full_approx_addr. exact Lsubqc.
                - split.
                  + intros [h' [obl' [beta' H7]]].
                    apply H5. exists h'. exists obl'. exists beta'.
                    revert H4 H7. apply subqc_full_approx_supports_asset_conv.
                    exact Lsubqc.
                  + change (ctree_rights_balanced (ctree_of_Block (bh, bd)) alpha b
                                                  (((stakeaddr bh, stakeassetid bh) ::nil) ++ sTxs_allinputs (blockdelta_stxl bd))
                                                  (stakeoutput bh ++ sTxs_alloutputs (blockdelta_stxl bd))).
                    apply ctree_rights_balanced_app.
                    * { intros rtot1 rtot2 h obl beta u H7 H8 H9.
                        assert (L8: ctree_supports_asset (h, (obl, owns b beta (Some u))) (prevledger bh) alpha).
                        { revert Lsubqc H4 H8. apply subqc_full_approx_supports_asset_conv. }
                        destruct (H6 rtot1 rtot2 h obl beta u H7 L8 H9) as [rtot3 [rtot4 [H10 [H11 H12]]]].
                        exists rtot3. exists rtot4.
                        repeat split.
                        - revert Lsubqc H10. apply subqc_rights_consumed.
                        - exact H11.
                        - exact H12.
                      }
                    * { apply ctree_rights_balanced_sTx_all.
                        intros tx H7.
                        destruct (HvBj tx H7) as [fee Hs].
                        generalize Hs. intros [_ [_ [[H8a H8b] _]]].
                        destruct (rights_mentioned_dec alpha b (tx_outputs tx)) as [D1|D1].
                        - destruct (H8a alpha b D1) as [_ [_ H9]].
                          exact H9.
                        - intros rtot1 rtot2 h obl beta u H9 H10 H11.
                          exists 0. exists 0.
                          rewrite (rights_unmentioned_no_rights_out alpha b _ D1) in H11.
                          rewrite (rights_unmentioned_no_rights_used alpha b _ D1) in H9.
                          subst rtot1. subst rtot2.
                          repeat split.
                          + apply ctree_supports_tx_can_support in Hs.
                            destruct Hs as [Hc1 _].
                            revert D1 Hc1 H8b.
                            clear.
                            intros D1.
                            generalize (tx_inputs tx) as inpl.
                            intros inpl. induction inpl as [|[gamma h] inpl IH].
                            * intros _ _. apply ctree_rights_consumed_nil.
                            * { intros Hc1 H8b.
                                assert (L9: exists oblu : obligation * preasset,
                                              ctree_supports_asset (h, oblu) (ctree_of_Block (bh, bd)) gamma).
                                { apply Hc1. now left. }
                                destruct L9 as [[obl u] L9a].
                                apply ctree_rights_consumed_skip with (obl := obl) (u := u).
                                - apply IH.
                                  + intros delta k H9. apply Hc1. now right.
                                  + intros delta c beta k obl' n H9. apply H8b. now right.
                                - exact L9a.
                                - intros [r2 H10]. subst u.
                                  apply D1. revert L9a. apply H8b.
                                  now left.
                              }
                          + omega.
                      }
              }
            * { generalize H1. intros H1a. apply In_In_dom_lem_2 in H1a.
                destruct (HvBj tx H1a) as [fee Hs].
                generalize Hs. intros [_ [_ [[H8a H8b] _]]].
                assert (L3: rights_mentioned alpha b (tx_outputs tx)).
                { right. exists beta2. exists obl2. exists n2. exact H2. }
                destruct (H8a _ _ L3) as [H4 [H5 H6]].
                split.
                - exact H4.
                - split.
                  + intros [h' [obl' [beta' H7]]].
                    apply H5. exists h'. exists obl'. exists beta'.
                    exact H7.
                  + change (ctree_rights_balanced (ctree_of_Block (bh, bd)) alpha b
                                                  (((stakeaddr bh, stakeassetid bh) ::nil) ++ sTxs_allinputs (blockdelta_stxl bd))
                                                  (stakeoutput bh ++ sTxs_alloutputs (blockdelta_stxl bd))).
                    apply ctree_rights_balanced_app.
                    * { intros rtot1 rtot2 h obl beta u H7 H8 H9.
                        destruct (rights_mentioned_dec alpha b (tx_outputs (coinstake bh))) as [D1|D1].
                        - destruct (HvBah4a alpha b D1) as [H4' [H5' H6']].
                          assert (L8: ctree_supports_asset (h, (obl, owns b beta (Some u))) (prevledger bh) alpha).
                          { revert Lsubqc H4' H8. apply subqc_full_approx_supports_asset_conv. }
                          destruct (H6' rtot1 rtot2 h obl beta u H7 L8 H9) as [rtot3 [rtot4 [H10 [H11 H12]]]].
                          exists rtot3. exists rtot4.
                          repeat split.
                          + revert Lsubqc H10. apply subqc_rights_consumed.
                          + exact H11.
                          + exact H12.
                        - exists 0. exists 0.
                          assert (L9a: rights_out b (stakeoutput bh) alpha = 0).
                          { exact (rights_unmentioned_no_rights_out alpha b _ D1). }
                          rewrite L9a in H9.
                          assert (L7a: count_rights_used (output_uses b (stakeoutput bh)) alpha = 0).
                          { exact (rights_unmentioned_no_rights_used alpha b _ D1). }
                          rewrite L7a in H7.
                          subst rtot1. subst rtot2.
                          repeat split.
                          + destruct HvBae as [a' [n [H10 _]]].
                            assert (L10: ctree_supports_asset
                                           (stakeassetid bh, (Some(a', n), currency (stake bh)))
                                           (ctree_of_Block (bh,bd)) (stakeaddr bh)).
                            { revert Lsubqc H10. apply subqc_supports_asset. }
                            assert (L11: ~exists r2, currency (stake bh) = rights b r2 alpha).
                            { intros [r2 H11]. discriminate H11. }
                            revert L10 L11. apply ctree_rights_consumed_skip.
                            apply ctree_rights_consumed_nil.
                          + omega.
                      }
                    * { apply ctree_rights_balanced_sTx_all.
                        intros tx' H7.
                        destruct (HvBj tx' H7) as [fee' Hs'].
                        generalize Hs'. intros [_ [_ [[H8a' H8b'] _]]].
                        destruct (rights_mentioned_dec alpha b (tx_outputs tx')) as [D1'|D1'].
                        - destruct (H8a' alpha b D1') as [_ [_ H9]].
                          exact H9.
                        - intros rtot1 rtot2 h obl beta u H9 H10 H11.
                          exists 0. exists 0.
                          rewrite (rights_unmentioned_no_rights_out alpha b _ D1') in H11.
                          rewrite (rights_unmentioned_no_rights_used alpha b _ D1') in H9.
                          subst rtot1. subst rtot2.
                          repeat split.
                          + apply ctree_supports_tx_can_support in Hs'.
                            destruct Hs' as [Hc1' _].
                            revert D1' Hc1' H8b'.
                            clear.
                            intros D1'.
                            generalize (tx_inputs tx') as inpl.
                            intros inpl. induction inpl as [|[gamma h] inpl IH].
                            * intros _ _. apply ctree_rights_consumed_nil.
                            * { intros Hc1' H8b'.
                                assert (L9: exists oblu : obligation * preasset,
                                              ctree_supports_asset (h, oblu) (ctree_of_Block (bh, bd)) gamma).
                                { apply Hc1'. now left. }
                                destruct L9 as [[obl u] L9a].
                                apply ctree_rights_consumed_skip with (obl := obl) (u := u).
                                - apply IH.
                                  + intros delta k H9. apply Hc1'. now right.
                                  + intros delta c beta k obl' n H9. apply H8b'. now right.
                                - exact L9a.
                                - intros [r2 H10]. subst u.
                                  apply D1'. revert L9a. apply H8b'.
                                  now left.
                              }
                          + omega.
                      }
              }
        - intros alpha b beta h obl n H1 H2.
          apply tx_of_Block_input_iff in H1.
          destruct H1 as [[H1a H1b]|[tx [sl [H1a H1b]]]].
          + exfalso. (*** impossible since the stake asset is currency, not rights. ***)
            generalize HT. intros [f [[_ [Hf2 _]] HTf]].
            generalize (ctree_supports_asset_In_statefun _ _ f _ HTf H2).
            intros H3.
            destruct HvBae as [a' [n' [H4 H5]]].
            assert (L4: ctree_supports_asset
                          (h, ((Some(a', n')), currency (stake bh))) 
                          (ctree_of_Block (bh,bd)) (stakeaddr bh)).
            { simpl in H1b. rewrite H1b.
              revert Lsubqc H4. apply subqc_supports_asset.
            }
            generalize (ctree_supports_asset_In_statefun _ _ f _ HTf L4).
            intros L4a.
            destruct (Hf2 h _ _ _ _ H3 L4a) as [_ H6].
            discriminate H6.
          + generalize H1a. intros H1aa. apply In_In_dom_lem_2 in H1aa.
            destruct (HvBj tx H1aa) as [fee [_ [_ [[_ H4b] _]]]].
            destruct (H4b _ _ _ _ _ _ H1b H2) as [H5|[gamma [obl2 [n2 H5]]]].
            * left. apply tx_of_Block_output_uses_iff.
              right. exists tx. exists sl. split; assumption.
            * right. exists gamma. exists obl2. exists n2.
              apply tx_of_Block_output_iff.
              right. exists tx. exists sl. split; assumption.
      }
    * { split.
        - revert Lsubqc HvBah HvBj.
          apply tx_of_Block_supported_lem_2.
        - split.
          + revert Lsubqc HvBah6 HvBj. clear.
            intros Lsubqc HvBah6 HvBj.
            intros alpha b obl beta r H1.
            apply tx_of_Block_output_iff in H1.
            destruct H1 as [H1|[tx [sl [H1 H2]]]].
            * { destruct (HvBah6 alpha b obl beta r H1) as [H7 H8].
                split.
                - revert H7. apply subqc_full_approx_addr. exact Lsubqc.
                - destruct H8 as [[h [beta' [obl' [r' [H9 H10]]]]]|[H9 H10]].
                  + left. exists h. exists beta'. exists obl'. exists r'.
                    split.
                    * revert H9. apply subqc_supports_asset. exact Lsubqc.
                    * apply tx_of_Block_input_iff.
                      left. simpl in H10. destruct H10 as [H10|[]].
                      inversion H10.
                      split; reflexivity.
                  + right. split.
                    * intros [h [beta' [obl' [r' H11]]]].
                      apply H9.
                      exists h. exists beta'. exists obl'. exists r'.
                      revert Lsubqc H7 H11.
                      apply subqc_full_approx_supports_asset_conv.
                    * apply tx_of_Block_output_uses_iff.
                      left. exact H10.
              }
            * { generalize H1. intros H1b. apply In_In_dom_lem_2 in H1b.
                destruct (HvBj tx H1b) as [fee [_ [_ [_ [_ [H6 _]]]]]].
                destruct (H6 alpha b obl beta r H2) as [H7 H8].
                split.
                - exact H7.
                - destruct H8 as [[h [beta' [obl' [r' [H9 H10]]]]]|[H9 H10]].
                  + left. exists h. exists beta'. exists obl'. exists r'.
                    split.
                    * exact H9.
                    * apply tx_of_Block_input_iff. right. exists tx. exists sl.
                      split; assumption.
                  + right. split.
                    * intros [h [beta' [obl' [r' H11]]]].
                      apply H9.
                      exists h. exists beta'. exists obl'. exists r'.
                      exact H11.
                    * apply tx_of_Block_output_uses_iff.
                      right. exists tx. exists sl.
                      split; assumption.
              }
          + split.
            * { intros alpha b H1.
                apply tx_of_Block_output_uses_iff in H1.
                destruct H1 as [H1|[tx [sl [H1 H2]]]].
                - destruct (HvBah7 alpha b H1) as [H3 H4].
                  split.
                  + revert Lsubqc H3. apply subqc_full_approx_addr.
                  + intros H5.
                    assert (L4: ~ (exists (h' : hashval) (beta' : addr) (obl' : obligation) (r' : option nat),
                                     ctree_supports_asset (h', (obl', owns true beta' r'))
                                                          (prevledger bh) alpha)).
                    { intros [h' [beta' [obl' [r' H6]]]].
                      apply H5. exists h'. exists beta'. exists obl'. exists r'.
                      revert Lsubqc H6. apply subqc_supports_asset.
                    }
                    destruct (H4 L4) as [beta [obl [r H6]]].
                    exists beta. exists obl. exists r.
                    apply tx_of_Block_output_iff.
                    left. exact H6.
                - generalize H1. intros H1b. apply In_In_dom_lem_2 in H1b.
                  destruct (HvBj tx H1b) as [fee [_ [_ [_ [_ [_ [H7 _]]]]]]].
                  destruct (H7 alpha b H2) as [H3 H4].
                  split.
                  + exact H3.
                  + intros H5.
                    assert (L4: ~ (exists (h' : hashval) (beta' : addr) (obl' : obligation) (r' : option nat),
                                     ctree_supports_asset (h', (obl', owns true beta' r'))
                                                          (ctree_of_Block (bh, bd)) alpha)).
                    { intros [h' [beta' [obl' [r' H6]]]].
                      apply H5. exists h'. exists beta'. exists obl'. exists r'.
                      exact H6.
                    }
                    destruct (H4 L4) as [beta [obl [r H6]]].
                    exists beta. exists obl. exists r.
                    apply tx_of_Block_output_iff.
                    right. exists tx. exists sl. split; assumption.
              }
            * { intros alpha h obl u H1 H2.
                apply tx_of_Block_input_iff in H1.
                destruct H1 as [[H1a H1b]|[tx [sl [H1a H1b]]]].
                - exfalso.
                  (*** This seemed to be a problematic case, but it's actually impossible.
                       It assumes the stakeassetid is for a bounty, but we know it's for currency. ***)
                  generalize HT. intros [f [[_ [Hf2 _]] HTf]].
                  generalize (ctree_supports_asset_In_statefun _ _ f _ HTf H2).
                  intros H3.
                  destruct HvBae as [a' [n [H4 H5]]].
                  assert (L4: ctree_supports_asset
                                (h, ((Some(a', n)), currency (stake bh))) 
                                (ctree_of_Block (bh,bd)) (stakeaddr bh)).
                  { rewrite H1b.
                    revert Lsubqc H4. apply subqc_supports_asset.
                  }
                  generalize (ctree_supports_asset_In_statefun _ _ f _ HTf L4).
                  intros L4a.
                  destruct (Hf2 h _ _ _ _ H3 L4a) as [_ H6].
                  discriminate H6.
                - generalize H1a. intros H1ab. apply In_In_dom_lem_2 in H1ab.
                  destruct (HvBj tx H1ab) as [fee [_ [_ [_ [_ [_ [_ H8]]]]]]].
                  destruct (H8 alpha h obl u H1b H2) as [H3 [h' [obl' [beta' [u' [H4 [H5 H6]]]]]]].
                  split.
                  + exact H3.
                  + exists h'. exists obl'. exists beta'. exists u'. repeat split.
                    * apply tx_of_Block_input_iff. right. exists tx. exists sl.
                      split; assumption.
                    * exact H5.
                    * apply tx_of_Block_output_iff. right. exists tx. exists sl.
                      split; assumption.
              }
      }
Qed.

Definition ledgerroot_valid (h:hashval) : Prop :=
  ctree_valid (ctreeH 162 h).

Definition ledgerroot_of_BlockChain {genh pbh plr ti n} (bc:@BlockChain genh pbh plr ti n) : hashval :=
match bc with
| BlockChainGen genti ({| newledgerroot := newledgerroot0 |}, _) =>
    newledgerroot0
| BlockChainSucc pbh0 plr0 ti0 _ _ ({| newledgerroot := newledgerroot0 |}, _) =>
    newledgerroot0
end.

Opaque tx_octree_trans.

Lemma ctree_hashroot_ctree_H {n} (h:hashval) :
  ctree_hashroot (ctreeH n h) = h.
destruct n; simpl; reflexivity.
Qed.

Opaque mtree_approx_fun_p.
Opaque ctree_mtree.
Opaque tx_of_Block.
Opaque mtree_hashroot.
Opaque ctree_hashroot.
Opaque ctree_cgraft.
Opaque cgraft_assoc.
Opaque subqm.

Lemma endledgerroot_plr_valid_lem1 pbh lroot ti (bh:@BlockHeader pbh lroot ti) bd (f:statefun) :
  mtree_approx_fun_p (ctree_mtree (ctreeH 162 lroot)) f ->
  ctree_hashroot (prevledger bh) = lroot ->
  cgraft_valid (prevledgergraft bd) ->
  mtree_approx_fun_p (ctree_mtree (ctree_of_Block (bh, bd))) f.
intros H1 H2 H3.
apply (mtree_hashroot_mtree_approx_fun_p (ctree_mtree (ctreeH 162 lroot))).
- change (mtree_hashroot (ctree_mtree (ctreeH 162 lroot)) =
          mtree_hashroot (ctree_mtree (ctree_of_Block (bh, bd)))).
  rewrite mtree_hashroot_ctree_hashroot.
  rewrite mtree_hashroot_ctree_hashroot.
  rewrite ctree_hashroot_ctree_H.
  unfold ctree_of_Block.
  assert (L1: subqc (prevledger bh) (ctree_cgraft (prevledgergraft bd) (prevledger bh))).
  { exact (ctree_cgraft_subqc (prevledgergraft bd) (prevledger bh) H3). }
  unfold subqc in L1.
  apply subqm_hashroot_eq in L1.
  rewrite mtree_hashroot_ctree_hashroot in L1.
  rewrite mtree_hashroot_ctree_hashroot in L1.
  rewrite H2 in L1.
  exact L1.
- exact H1.
Qed.

Theorem endledgerroot_plr_valid rewfn check_hit targetf {genlr pbh plr ti n}
      (bc : @BlockChain genlr pbh plr ti n) :
  ledgerroot_valid genlr ->
  valid_BlockChain rewfn check_hit targetf bc ->
  ledgerroot_valid plr.
intros H1. induction bc as [ti [bh bd]|pbh plr ti n bc IH [bh bd]].
- intros H2. generalize H2. intros [[H2aa [H2ab [H2ac [H2ad [H2ae [H2af [H2ag H2ah]]]]]]] [H2b [H2c [H2d [H2e [H2f [H2g [H2h [H2i [H2j [H2k H2l]]]]]]]]]]].
  assert (LT: ctree_valid (ctree_of_Block (bh,bd))).
  { unfold ctree_of_Block. apply ctree_valid_cgraft_valid.
    - revert H1. unfold ledgerroot_valid. unfold ctree_valid.
      apply mtree_hashroot_eq_valid.
      rewrite mtree_hashroot_ctree_hashroot.
      rewrite mtree_hashroot_ctree_hashroot.
      rewrite ctree_hashroot_ctree_H.
      f_equal. exact H2ad.
    - exact H2i.
  }
  destruct H2l as [T [H2la H2lb]].
  change (ledgerroot_valid (newledgerroot bh)).
  rewrite <- H2la.
  unfold ledgerroot_valid.
  unfold ctree_valid.
  assert (L1: octree_supports_tx (tx_of_Block (bh,bd)) (Some (ctree_of_Block (bh,bd))) 0 (rewfn 0)).
  { exact (tx_of_Block_supported 0 (rewfn 0) check_hit targetf (bh,bd) LT H2). }
  apply (mtree_hashroot_eq_valid (ctree_mtree T)).
  + rewrite mtree_hashroot_ctree_hashroot.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite ctree_hashroot_ctree_H.
    reflexivity.
  + destruct H1 as [f [H1a H1b]].
    assert (LTf: octree_approx_fun_p (Some (ctree_of_Block (bh,bd))) f).
    { exact (endledgerroot_plr_valid_lem1 None genlr ti bh bd f H1b H2ad H2i). }
    exists (tx_statefun_trans (tx_of_Block (bh,bd)) f). split.
    * { apply sf_tx_valid_thm with (m := 0) (fee := 0) (rew := (rewfn 0)).
        - exact H1a.
        - revert H2. apply tx_of_Block_valid.
        - assert (L2: mtree_supports_tx (tx_of_Block (bh, bd))
                                        (octree_mtree (Some (ctree_of_Block (bh, bd)))) 0 
                                        (rewfn 0)).
          { revert L1. apply octree_mtree_supports_tx. }
          apply mtree_supports_tx_statefun with (f := f) in L2.
          + exact L2.
          + destruct H1a as [_ [Hf2 _]]. exact Hf2.
          + unfold octree_approx_fun_p in LTf.
            exact LTf.
      }
    * { assert (L4: mtree_approx_fun_p (octree_mtree (Some T)) (tx_statefun_trans (tx_of_Block (bh, bd)) f)).
        { rewrite <- H2lb.
          set (tx' := (tx_of_Block (bh,bd))).
          set (T' := (ctree_of_Block (bh,bd))).
          assert (L5: octree_approx_fun_p (tx_octree_trans tx' (Some T')) (tx_statefun_trans tx' f)).
          { apply (octree_approx_trans tx' (Some T') f 0 (rewfn 0)).
            - exact H1a.
            - unfold tx'. unfold T'. revert H2. apply tx_of_Block_supported.
              exact LT.
            - unfold T'. exact LTf.
          }
          unfold octree_approx_fun_p in L5.
          exact L5.
        }
        unfold octree_mtree in L4.
        exact L4.
      }
- intros [H3 H2].
  generalize H2.
  intros [[H2aa [H2ab [H2ac [H2ad [H2ae [H2af [H2ag H2ah]]]]]]] [H2b [H2c [H2d [H2e [H2f [H2g [H2h [H2i [H2j [H2k H2l]]]]]]]]]]].
  assert (LT: ctree_valid (ctree_of_Block (bh,bd))).
  { unfold ctree_of_Block. apply ctree_valid_cgraft_valid.
    - generalize (IH H3). unfold ledgerroot_valid. unfold ctree_valid.
      apply mtree_hashroot_eq_valid.
      rewrite mtree_hashroot_ctree_hashroot.
      rewrite mtree_hashroot_ctree_hashroot.
      rewrite ctree_hashroot_ctree_H.
      f_equal. exact H2ad.
    - exact H2i.
  }
  destruct H2l as [T [H2la H2lb]].
  change (ledgerroot_valid (newledgerroot bh)).
  rewrite <- H2la.
  unfold ledgerroot_valid.
  unfold ctree_valid.
  assert (L1: octree_supports_tx (tx_of_Block (bh,bd)) (Some (ctree_of_Block (bh,bd))) 0 (rewfn (S n))).
  { exact (tx_of_Block_supported (S n) (rewfn (S n)) check_hit targetf (bh,bd) LT H2). }
  apply (mtree_hashroot_eq_valid (ctree_mtree T)).
  + rewrite mtree_hashroot_ctree_hashroot.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite ctree_hashroot_ctree_H.
    reflexivity.
  + destruct (IH H3) as [f [H1a H1b]].
    assert (LTf: octree_approx_fun_p (Some (ctree_of_Block (bh,bd))) f).
    { exact (endledgerroot_plr_valid_lem1 _ _ ti bh bd f H1b H2ad H2i). }
    exists (tx_statefun_trans (tx_of_Block (bh,bd)) f). split.
    * { apply sf_tx_valid_thm with (m := (S n)) (fee := 0) (rew := (rewfn (S n))).
        - exact H1a.
        - revert H2. apply tx_of_Block_valid.
        - assert (L2: mtree_supports_tx (tx_of_Block (bh, bd))
                                        (octree_mtree (Some (ctree_of_Block (bh, bd)))) 0 
                                        (rewfn (S n))).
          { revert L1. apply octree_mtree_supports_tx. }
          apply mtree_supports_tx_statefun with (f := f) in L2.
          + exact L2.
          + destruct H1a as [_ [Hf2 _]]. exact Hf2.
          + unfold octree_approx_fun_p in LTf.
            exact LTf.
      }
    * { assert (L4: mtree_approx_fun_p (octree_mtree (Some T)) (tx_statefun_trans (tx_of_Block (bh, bd)) f)).
        { rewrite <- H2lb.
          set (tx' := (tx_of_Block (bh,bd))).
          set (T' := (ctree_of_Block (bh,bd))).
          assert (L5: octree_approx_fun_p (tx_octree_trans tx' (Some T')) (tx_statefun_trans tx' f)).
          { apply (octree_approx_trans tx' (Some T') f 0 (rewfn (S n))).
            - exact H1a.
            - unfold tx'. unfold T'. revert H2. apply tx_of_Block_supported.
              exact LT.
            - unfold T'. exact LTf.
          }
          unfold octree_approx_fun_p in L5.
          exact L5.
        }
        unfold octree_mtree in L4.
        exact L4.
      }
Qed.

Theorem endledgerroot_valid rewfn check_hit targetf {genlr pbh plr ti n}
      (bc : @BlockChain genlr pbh plr ti n) :
  ledgerroot_valid genlr ->
  valid_BlockChain rewfn check_hit targetf bc ->
  ledgerroot_valid (ledgerroot_of_BlockChain bc).
intros H1 H2.
generalize (endledgerroot_plr_valid rewfn check_hit targetf bc H1 H2).
intros H3.
destruct bc as [ti [bh bd]|pbh plr ti n bc [bh bd]].
- exact H3.
- exact H3.
Qed.

Fixpoint units_as_of_block (initdistr:nat) (rewfn:nat -> nat) (blockheight:nat) : nat :=
match blockheight with
| O => initdistr
| S n => units_as_of_block initdistr rewfn n + rewfn n
end.

Opaque sf_valid.
Opaque tx_statefun_trans.
Opaque tx_octree_trans.
Opaque mtree_approx_fun_p.

Theorem endledgerroot_plr_sum_correct initdistr al bl rewfn check_hit targetf {genlr pbh plr ti n}
      (bc : @BlockChain genlr pbh plr ti n) :
  ledgerroot_valid genlr ->
  octree_totalassets (Some (ctreeH 162 genlr)) al ->
  asset_value_sum al = initdistr ->
  valid_BlockChain rewfn check_hit targetf bc ->
  octree_totalassets (Some (ctreeH 162 plr)) bl ->
  asset_value_sum bl = units_as_of_block initdistr rewfn (S n).
intros H1 H2 H3. revert bl.
induction bc as [ti [bh bd]|pbh plr ti n bc IH [bh bd]].
- intros bl H4 H5.
  simpl. unfold valid_BlockChain in H4.
  generalize H4.
  intros [[H4aa [H4ab [H4ac [H4ad [H4ae [H4af [H4ag H4ah]]]]]]] [H4b [H4c [H4d [H4e [H4f [H4g [H4h [H4i [H4j [H4k [T [HT1 HT2]]]]]]]]]]]]].
  assert (L0: ctree_hashroot (ctree_of_Block(bh,bd)) = genlr).
  { transitivity (ctree_hashroot (prevledger bh)).
    - unfold ctree_of_Block. symmetry.
      apply subqc_hashroot_eq. apply ctree_cgraft_subqc. exact H4i.
    - exact H4ad.
  }
  assert (L1: octree_valid (Some (ctree_of_Block (bh, bd)))).
  { unfold octree_valid. revert H1. unfold ledgerroot_valid. unfold ctree_valid.
    apply mtree_hashroot_eq_valid.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite L0.
    rewrite ctree_hashroot_ctree_H.
    reflexivity.
  }
  assert (L2: tx_valid 0 (tx_of_Block (bh, bd))).
  { revert H4. apply tx_of_Block_valid. }
  assert (L3: octree_supports_tx (tx_of_Block (bh, bd)) (Some (ctree_of_Block (bh, bd))) 0 (rewfn 0)).
  { unfold octree_supports_tx. revert L1 H4. unfold octree_valid. apply tx_of_Block_supported. }
  generalize L1. intros [f [Hf HTf]].
  assert (L4: mtree_approx_fun_p (ctree_mtree (ctreeH 162 genlr)) f).
  { revert HTf. apply mtree_hashroot_mtree_approx_fun_p.
    rewrite mtree_hashroot_ctree_hashroot. rewrite L0.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite ctree_hashroot_ctree_H.
    reflexivity.
  }
  assert (L5: octree_totalassets (Some (ctree_of_Block (bh, bd))) al).
  { unfold octree_totalassets. unfold octree_mtree.
    apply (mtree_approx_fun_p_totalassets _ _ _ HTf).
    revert H2. unfold octree_totalassets. unfold octree_mtree.
    revert L4. clear. apply mtree_approx_fun_p_totalassets.
  }
  assert (L6: octree_approx_fun_p
                (tx_octree_trans (tx_of_Block (bh, bd))
                                 (Some (ctree_of_Block (bh, bd))))
                (tx_statefun_trans (tx_of_Block (bh, bd)) f)).
  { apply (octree_approx_trans (tx_of_Block (bh,bd)) (Some (ctree_of_Block (bh,bd))) f 0 (rewfn 0) Hf L3).
    unfold octree_approx_fun_p. unfold octree_mtree.
    exact HTf.
  }
  assert (L7: octree_approx_fun_p (Some T) (tx_statefun_trans (tx_of_Block (bh, bd)) f)).
  { unfold octree_approx_fun_p. rewrite <- HT2.
    exact L6.
  }
  assert (L8: octree_totalassets (tx_octree_trans (tx_of_Block (bh, bd)) (Some (ctree_of_Block (bh, bd)))) bl).
  { rewrite HT2.
    unfold octree_totalassets. unfold octree_mtree.
    apply (mtree_approx_fun_p_totalassets _ _ _ L7).
    revert H5.
    unfold octree_totalassets. unfold octree_mtree.
    apply mtree_approx_fun_p_totalassets.
    revert L7. unfold octree_approx_fun_p.
    apply mtree_hashroot_mtree_approx_fun_p.
    unfold octree_mtree.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite ctree_hashroot_ctree_H.
    rewrite HT1. reflexivity.
  }
  generalize (octree_tx_asset_value_sum 0 (Some (ctree_of_Block (bh,bd))) (tx_of_Block (bh,bd)) 0 (rewfn 0) al bl L1 L2 L3 L5 L8).
  rewrite H3.
  assert (L9: asset_value_sum bl + 0 = asset_value_sum bl).
  { clear. omega. }
  rewrite L9. exact (fun H => H).
- intros bl [H4 H5] H6.
  generalize H5.
  intros [[H5aa [H5ab [H5ac [H5ad [H5ae [H5af [H5ag H5ah]]]]]]] [H5b [H5c [H5d [H5e [H5f [H5g [H5h [H5i [H5j [H5k [T [HT1 HT2]]]]]]]]]]]]].
  assert (Lplr: ledgerroot_valid plr).
  { revert H1 H4. apply endledgerroot_plr_valid. }
  generalize Lplr. intros [f [Hf Hplrf]].
  assert (LIH: asset_value_sum (totalassets_ f) = units_as_of_block initdistr rewfn (S n)).
  { apply IH.
    - exact H4.
    - unfold octree_totalassets. unfold octree_mtree.
      apply (mtree_approx_fun_p_totalassets _ _ _ Hplrf).
      reflexivity.
  }
  change (asset_value_sum bl = units_as_of_block initdistr rewfn (S n) + rewfn (S n)).
  rewrite <- LIH.
  assert (L0: ctree_hashroot (ctree_of_Block(bh,bd)) = plr).
  { transitivity (ctree_hashroot (prevledger bh)).
    - unfold ctree_of_Block. symmetry.
      apply subqc_hashroot_eq. apply ctree_cgraft_subqc. exact H5i.
    - exact H5ad.
  }
  assert (L1: octree_valid (Some (ctree_of_Block (bh, bd)))).
  { unfold octree_valid. revert Lplr. unfold ledgerroot_valid. unfold ctree_valid.
    apply mtree_hashroot_eq_valid.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite L0.
    rewrite ctree_hashroot_ctree_H.
    reflexivity.
  }
  assert (L2: tx_valid (S n) (tx_of_Block (bh, bd))).
  { revert H5. apply tx_of_Block_valid. }
  assert (L3: octree_supports_tx (tx_of_Block (bh, bd)) (Some (ctree_of_Block (bh, bd))) 0 (rewfn (S n))).
  { unfold octree_supports_tx. revert L1 H5. unfold octree_valid. apply tx_of_Block_supported. }
  assert (L4: mtree_approx_fun_p (ctree_mtree (ctree_of_Block (bh,bd))) f).
  { revert Hplrf. apply mtree_hashroot_mtree_approx_fun_p.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite mtree_hashroot_ctree_hashroot. rewrite L0.
    rewrite ctree_hashroot_ctree_H.
    reflexivity.
  }
  assert (L5: octree_totalassets (Some (ctree_of_Block (bh, bd))) (totalassets_ f)).
  { unfold octree_totalassets. unfold octree_mtree.
    apply (mtree_approx_fun_p_totalassets _ _ _ L4).
    reflexivity.
  }
  assert (L6: octree_approx_fun_p
                (tx_octree_trans (tx_of_Block (bh, bd))
                                 (Some (ctree_of_Block (bh, bd))))
                (tx_statefun_trans (tx_of_Block (bh, bd)) f)).
  { apply (octree_approx_trans (tx_of_Block (bh,bd)) (Some (ctree_of_Block (bh,bd))) f 0 (rewfn (S n)) Hf L3).
    unfold octree_approx_fun_p. unfold octree_mtree.
    exact L4.
  }
  assert (L7: octree_approx_fun_p (Some T) (tx_statefun_trans (tx_of_Block (bh, bd)) f)).
  { unfold octree_approx_fun_p. rewrite <- HT2.
    exact L6.
  }
  assert (L8: octree_totalassets (tx_octree_trans (tx_of_Block (bh, bd)) (Some (ctree_of_Block (bh, bd)))) bl).
  { rewrite HT2.
    unfold octree_totalassets. unfold octree_mtree.
    apply (mtree_approx_fun_p_totalassets _ _ _ L7).
    revert H6.
    unfold octree_totalassets. unfold octree_mtree.
    apply mtree_approx_fun_p_totalassets.
    revert L7. unfold octree_approx_fun_p.
    apply mtree_hashroot_mtree_approx_fun_p.
    unfold octree_mtree.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite ctree_hashroot_ctree_H.
    rewrite HT1. reflexivity.
  }
  generalize (octree_tx_asset_value_sum (S n) (Some (ctree_of_Block (bh,bd))) (tx_of_Block (bh,bd)) 0 (rewfn (S n)) (totalassets_ f) bl L1 L2 L3 L5 L8).
  assert (L9: asset_value_sum bl + 0 = asset_value_sum bl).
  { clear. omega. }
  rewrite L9. exact (fun H => H).
Qed.
