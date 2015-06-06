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

(*** por_trm alpha h m : m is a trm (using Gns to summarize some subterms) with termaddr alpha and h is the asset id of an ownership asset held at alpha. ***)
(*** por_doc alpha h d : d is a partial document with a hashroot with pubaddr alpha and h is the asset id of a publication held at alpha. ***)
Inductive por : Type :=
| por_trm : termaddr -> hashval -> trm -> por
| por_doc : pubaddr -> hashval -> partialdoc -> por
.

(*** ledgerroot hashval is the combined hash for the theory tree, signature tree and ledger tree:
     (hashopair2 <theorytreeoptionhashval> (hashopair2 <signatreeoptionhashval> <ledgerroot>))
     See comments marked [+].
 ***)
Record BlockHeader {prevblockhash : option hashval} {prevledgerroot : hashval} {ti:targetinfo} : Type :=
  mkBlockHeader
    {
      newledgerroot : hashval;
      timestamp : nat;
      stake : nat;
      stakeaddr : payaddr;
      stakeassetid : hashval;
      retrievable : option por;
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
  ((payaddr_addr (stakeaddr bh),stakeassetid bh)::nil,stakeoutput bh).

Definition hitfun : Type  := option hashval -> nat -> nat -> nat -> payaddr -> option por -> Prop.

Definition targetfun : Type := targetinfo -> nat.

Definition hash_BlockHeader {pbh plr ti} (bh:@BlockHeader pbh plr ti) : hashval :=
hashopair2 pbh (hashlist (newledgerroot bh::hashnat (timestamp bh)::hashtx (coinstake bh)::nil)).

(*** A currency asset can be used to stake as long as it will not mature in the next 100 blocks. (100 is arbitrary, of course.) ***)
Definition not_close_to_mature : nat := 100.

(*** The output from staking cannot be spent until 100 blocks later. Again, 100 is arbitrary here. ***)
Definition maturation_post_staking : nat := 100.

(*** The output must age 100 blocks before staking. Again, 100 is arbitrary here. ***)
Definition maturation_pre_staking : nat := 100.

Definition valid_BlockHeader (tht: option (ttree 160)) (sigt: option (stree 160)) (blockheight:nat) (rew:nat) (check_hit : hitfun) (targetf : targetfun) {pbh plr ti} (bh:@BlockHeader pbh plr ti) : Prop :=
  timestamp bh > targetinfo_timestamp ti
  /\
  check_signat (hash_BlockHeader bh) (blocksignat bh) (stakeaddr bh)
  /\
  check_hit pbh (timestamp bh) (targetf ti) (stake bh) (stakeaddr bh) (retrievable bh)
  /\
  hashopair2 (ottree_hashroot tht) (hashopair2 (ostree_hashroot sigt) (ctree_hashroot (prevledger bh))) = plr (*** [+] ***)
  /\
  ((exists bday,
      ctree_supports_asset (stakeassetid bh,(bday,(None,currency (stake bh)))) (prevledger bh) (payaddr_addr (stakeaddr bh))
      /\
      (bday + maturation_pre_staking <= blockheight \/ bday = 0))
   \/
   (exists bday a n,
      ctree_supports_asset (stakeassetid bh,(bday,(Some(a,n),currency (stake bh)))) (prevledger bh) (payaddr_addr (stakeaddr bh))
      /\
      bday + maturation_pre_staking <= blockheight
      /\
      n > blockheight + not_close_to_mature))
  /\
  (*** The stake outputs must be valid. ***)
  tx_outputs_valid (stakeoutput bh)
  /\
  (*** The stake outputs must explicitly say that they cannot be spent until at least blockheight + maturation_post_staking. ***)
  (forall alpha obl u, In (alpha,(obl,u)) (stakeoutput bh) -> exists a n, obl = Some(a,n) /\ n > blockheight + maturation_post_staking)
  /\
  (*** The ctree of the previous ledger supports the declared coinstake tx. ***)
  ctree_supports_tx tht sigt blockheight (coinstake bh) (prevledger bh) 0 (rew + totalfees bh).

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
  ((payaddr_addr (stakeaddr bh),stakeassetid bh)::sTxs_allinputs (blockdelta_stxl bd),stakeoutput bh ++ sTxs_alloutputs (blockdelta_stxl bd)).

Definition valid_Block tht sigt (blockheight:nat) (rew:nat) (check_hit : hitfun) (targetf : targetfun) {pbh plr ti} (b:@Block pbh plr ti) : Prop :=
  let (bh,bd) := b in
  (*** The header is valid. ***)
  valid_BlockHeader tht sigt blockheight rew check_hit targetf bh
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
  (*** Each transaction in the delta is valid. ***)
  (forall stx, In stx (blockdelta_stxl bd) -> tx_valid (fst stx))
  /\
  (*** No transaction has the stake asset as an input. ***)
  (forall tx, In_dom tx (blockdelta_stxl bd) -> ~ In (payaddr_addr (stakeaddr bh),stakeassetid bh) (tx_inputs tx))
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
              -> exists fee, ctree_supports_tx tht sigt blockheight tx (ctree_of_Block (bh,bd)) fee 0)
  (*** The total inputs and outputs match up with the declared fee. ***)
  /\
  (exists utot:nat,
     ctree_asset_value_in (ctree_of_Block (bh,bd)) (sTxs_allinputs (blockdelta_stxl bd)) utot
     /\
     asset_value_out (sTxs_alloutputs (blockdelta_stxl bd)) + (totalfees bh) + out_burncost (sTxs_alloutputs (blockdelta_stxl bd)) = utot)
  /\
  exists T:ctree 162,
    newledgerroot bh = hashopair2 (ottree_hashroot (tx_update_ottree (tx_of_Block (bh,bd)) tht)) (hashopair2 (ostree_hashroot (tx_update_ostree (tx_of_Block (bh,bd)) sigt)) (ctree_hashroot T)) (*** [+] ***)
    /\ tx_octree_trans blockheight (tx_of_Block (bh,bd)) (Some (ctree_of_Block (bh,bd))) = Some T.

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
| BlockChainGen genti b => exists tht sigt, valid_Block tht sigt 0 (rewfn 0) check_hit targetf b
| BlockChainSucc pbh plr ti n bc b => valid_BlockChain rewfn check_hit targetf bc /\ exists tht sigt, valid_Block tht sigt (S n) (rewfn (S n)) check_hit targetf b
end.

Fixpoint valid_BlockHeaderChain (rewfn:nat -> nat) (check_hit:hitfun) (targetf:targetfun) {genlr pbh plr ti n} (bc : @BlockHeaderChain genlr pbh plr ti n) : Prop :=
match bc with
| BlockHeaderChainGen genti bh => exists tht sigt, valid_BlockHeader tht sigt 0 (rewfn 0) check_hit targetf bh
| BlockHeaderChainSucc pbh plr ti n bc bh => valid_BlockHeaderChain rewfn check_hit targetf bc /\ exists tht sigt, valid_BlockHeader tht sigt (S n) (rewfn (S n)) check_hit targetf bh
end.

Lemma tx_of_Block_valid tht sigt blockheight rew check_hit targetf {pbh plr ti} (b:@Block pbh plr ti) :
  valid_Block tht sigt blockheight rew check_hit targetf b ->
  tx_valid (tx_of_Block b).
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
  + split;[|split;[|split]].
    * { intros alpha a b beta r H1.
        simpl in H1. apply in_app_or in H1.
        destruct H1 as [H1|H1].
        - destruct HvBaf as [_ HvBaf2].
          revert H1. apply HvBaf2.
        - apply sTxs_alloutputs_iff in H1. destruct H1 as [[inpl outpl] [H2 H3]].
          apply In_In_dom_lem in H2.
          destruct H2 as [sl H2].
          destruct (HvBd ((inpl,outpl),sl) H2) as [_ [_ H4]].
          revert H3. apply H4.
      }
    * { intros alpha obl beta nonce thy H1.
        simpl in H1. apply in_app_or in H1.
        destruct H1 as [H1|H1].
        - destruct HvBaf as [_ HvBaf2].
          revert H1. apply HvBaf2.
        - apply sTxs_alloutputs_iff in H1. destruct H1 as [[inpl outpl] [H2 H3]].
          apply In_In_dom_lem in H2.
          destruct H2 as [sl H2].
          destruct (HvBd ((inpl,outpl),sl) H2) as [_ [_ H4]].
          revert H3. apply H4.
      }
    * { intros alpha obl beta nonce th s H1.
        simpl in H1. apply in_app_or in H1.
        destruct H1 as [H1|H1].
        - destruct HvBaf as [_ HvBaf2].
          revert H1. apply HvBaf2.
        - apply sTxs_alloutputs_iff in H1. destruct H1 as [[inpl outpl] [H2 H3]].
          apply In_In_dom_lem in H2.
          destruct H2 as [sl H2].
          destruct (HvBd ((inpl,outpl),sl) H2) as [_ [_ H4]].
          revert H3. apply H4.
      }
    * { intros alpha obl beta nonce th d H1.
        simpl in H1. apply in_app_or in H1.
        destruct H1 as [H1|H1].
        - destruct HvBaf as [_ HvBaf2].
          revert H1. apply HvBaf2.
        - apply sTxs_alloutputs_iff in H1. destruct H1 as [[inpl outpl] [H2 H3]].
          apply In_In_dom_lem in H2.
          destruct H2 as [sl H2].
          destruct (HvBd ((inpl,outpl),sl) H2) as [_ [_ H4]].
          revert H3. apply H4.
      }
Qed.

Lemma tx_of_Block_input_iff alpha h {pbh plr ti} (b : @Block pbh plr ti) :
  In (alpha,h) (tx_inputs (tx_of_Block b))
  <->
  ((alpha = payaddr_addr (stakeaddr (fst b)) /\ h = stakeassetid (fst b))
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
   exists tx sli slo, In (tx,(sli,slo)) (blockdelta_stxl (snd b)) /\ In alpha (output_uses c (tx_outputs tx))).
destruct b as [bh bd].
assert (L1: In alpha (output_uses c (sTxs_alloutputs (blockdelta_stxl bd)))
            <->
            exists (tx : Tx) (sli slo : list gensignat),
              In (tx, (sli,slo)) (blockdelta_stxl bd) /\
              In alpha (output_uses c (tx_outputs tx))).
{ generalize (blockdelta_stxl bd) as stxl.
  induction stxl as [|[[inpl outpl] [sli slo]] stxl IH].
  - simpl. split.
    + tauto.
    + intros [tx [sli [slo [[] _]]]].
  - simpl. split.
    + intros H1. apply output_uses_app_or in H1. destruct H1 as [H1|H1].
      * exists (inpl,outpl). exists sli. exists slo. simpl. tauto.
      * apply IH in H1. destruct H1 as [tx [sli' [slo' [H2 H3]]]].
        exists tx. exists sli'. exists slo'. tauto.
    + intros [tx [sli' [slo' [[H1|H1] H2]]]].
      * apply output_uses_app_or. left. inversion H1.
        subst tx. exact H2.
      * apply output_uses_app_or. right. apply IH.
        exists tx. exists sli'. exists slo'. tauto.
}
simpl. split.
- intros H1. apply output_uses_app_or in H1. destruct H1 as [H1|H1].
  + now left.
  + right. now apply L1.
- intros [H1|H1].
  + apply output_uses_app_or. now left.
  + apply output_uses_app_or. right. apply L1. exact H1.
Qed.

Lemma tx_of_Block_output_creates_iff alpha c {pbh plr ti} (b : @Block pbh plr ti) :
 In alpha (output_creates c (tx_outputs (tx_of_Block b)))
 <->
 (In alpha (output_creates c (stakeoutput (fst b)))
  \/
   exists tx sli slo, In (tx,(sli,slo)) (blockdelta_stxl (snd b)) /\ In alpha (output_creates c (tx_outputs tx))).
destruct b as [bh bd].
assert (L1: In alpha (output_creates c (sTxs_alloutputs (blockdelta_stxl bd)))
            <->
            exists (tx : Tx) (sli slo : list gensignat),
              In (tx, (sli,slo)) (blockdelta_stxl bd) /\
              In alpha (output_creates c (tx_outputs tx))).
{ generalize (blockdelta_stxl bd) as stxl.
  induction stxl as [|[[inpl outpl] [sli slo]] stxl IH].
  - simpl. split.
    + tauto.
    + intros [tx [sli [slo [[] _]]]].
  - simpl. split.
    + intros H1. apply output_creates_app_or in H1. destruct H1 as [H1|H1].
      * exists (inpl,outpl). exists sli. exists slo. simpl. tauto.
      * apply IH in H1. destruct H1 as [tx [sli' [slo' [H2 H3]]]].
        exists tx. exists sli'. exists slo'. tauto.
    + intros [tx [sli' [slo' [[H1|H1] H2]]]].
      * apply output_creates_app_or. left. inversion H1.
        subst tx. exact H2.
      * apply output_creates_app_or. right. apply IH.
        exists tx. exists sli'. exists slo'. tauto.
}
simpl. split.
- intros H1. apply output_creates_app_or in H1. destruct H1 as [H1|H1].
  + now left.
  + right. now apply L1.
- intros [H1|H1].
  + apply output_creates_app_or. now left.
  + apply output_creates_app_or. right. apply L1. exact H1.
Qed.

Opaque ctree_supports_addr.
Transparent output_uses.

Lemma ctree_rights_balanced_app (T:ctree 162) alpha b inpl1 outpl1 inpl2 outpl2 :
  ctree_rights_balanced T alpha b inpl1 outpl1 ->
  ctree_rights_balanced T alpha b inpl2 outpl2 ->
  ctree_rights_balanced T alpha b (inpl1 ++ inpl2) (outpl1 ++ outpl2).
unfold ctree_rights_balanced. intros H1 H2 rtot1 rtot2 h bday obl beta u H3 H4 H5.
rewrite output_uses_app in H3. rewrite count_rights_used_app in H3.
rewrite rights_out_app in H5.
assert (L3: exists rtot3 rtot4 : nat,
              ctree_rights_consumed b alpha T inpl1 rtot3 /\
              rtot4 * u <= units_sent_to_addr (payaddr_addr beta) outpl1 /\
              count_rights_used (output_uses b outpl1) alpha +
              rights_out b outpl1 alpha = rtot3 + rtot4).
{ apply (H1 (count_rights_used (output_uses b (outpl1)) alpha) (rights_out b outpl1 alpha) h bday obl beta u).
    - reflexivity.
    - exact H4.
    - reflexivity.
}
assert (L4: exists rtot3 rtot4 : nat,
              ctree_rights_consumed b alpha T inpl2 rtot3 /\
              rtot4 * u <= units_sent_to_addr (payaddr_addr beta) outpl2 /\
              count_rights_used (output_uses b outpl2) alpha +
              rights_out b outpl2 alpha = rtot3 + rtot4).
{ apply (H2 (count_rights_used (output_uses b (outpl2)) alpha) (rights_out b outpl2 alpha) h bday obl beta u).
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
- simpl. intros _ rtot1 rtot2 h bday obl beta u H1 H2 H3.
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
Lemma tx_of_Block_supported_lem_1 tht sigt blockheight rew {pbh plr ti} (bh:@BlockHeader pbh plr ti) (bd:BlockDelta) utot :
  ctree_valid (ctree_of_Block (bh, bd)) ->
  subqc (prevledger bh) (ctree_of_Block (bh, bd)) ->
  ((exists bday,
      ctree_supports_asset (stakeassetid bh,(bday,(None,currency (stake bh)))) (prevledger bh) (payaddr_addr (stakeaddr bh))
      /\
      (bday + maturation_pre_staking <= blockheight \/ bday = 0))
   \/
   (exists (bday : nat) (a : payaddr) (n : nat),
      ctree_supports_asset
        (stakeassetid bh, (bday,(Some(a,n), currency (stake bh))))
        (prevledger bh) (payaddr_addr (stakeaddr bh)) /\
      bday + maturation_pre_staking <= blockheight /\
      n > blockheight + not_close_to_mature)) ->
  ctree_supports_tx tht sigt blockheight (coinstake bh) (prevledger bh) 0 (rew + totalfees bh) ->
  asset_value_out (sTxs_alloutputs (blockdelta_stxl bd)) + totalfees bh + out_burncost (sTxs_alloutputs (blockdelta_stxl bd)) = utot ->
  asset_value_out (tx_outputs (tx_of_Block (bh, bd))) + 0 + out_burncost (tx_outputs (tx_of_Block (bh,bd))) =
  stake bh + utot + rew.
  intros HT Lsubqc HvBae HvBah H3.
  simpl. rewrite asset_value_out_app.
  destruct HvBah as [_ [[utot2 [H4 H5]] _]].
  assert (L2: utot2 = stake bh).
  { revert HT Lsubqc HvBae H4. clear.
    intros [f [[_ [Hf2 _]] HTf]] Lsubqc.
    intros [[bday [H4 H5]]|[bday [a' [n [H4 [H5a H5]]]]]].
    - simpl. intros H1. inversion H1.
      + inversion H2.
        assert (L2a : ctree_supports_asset
                        (stakeassetid bh, (bday,(None, currency (stake bh)))) 
                        (ctree_of_Block (bh,bd))
                        (payaddr_addr (stakeaddr bh))).
        { revert H4. apply subqc_supports_asset. exact Lsubqc. }
        assert (L2b : ctree_supports_asset a
                                           (ctree_of_Block (bh,bd))
                                           (payaddr_addr (stakeaddr bh))).
        { revert H6. apply subqc_supports_asset. exact Lsubqc. }
        generalize (ctree_supports_asset_In_statefun _ _ f _ HTf L2a).
        intros L2a'.
        generalize (ctree_supports_asset_In_statefun _ _ f _ HTf L2b).
        intros L2b'.
        rewrite <- H0 in L2a'.
        destruct a as [h' [obl' u']].
        simpl in H9. rewrite <- H9 in L2b'. rewrite <- H0 in L2b'.
        destruct (Hf2 h (payaddr_addr (stakeaddr bh)) (bday,(None,currency (stake bh))) (payaddr_addr (stakeaddr bh)) (obl',u') L2a' L2b') as [_ H11].
        inversion H11. subst u'.
        unfold asset_value in H8. simpl in H8. inversion H8.
        inversion H3. omega.
      + exfalso.
        assert (L2a : ctree_supports_asset
                        (stakeassetid bh, (bday,(None, currency (stake bh))))
                        (ctree_of_Block (bh,bd))
                        (payaddr_addr (stakeaddr bh))).
        { revert H4. apply subqc_supports_asset. exact Lsubqc. }
        assert (L2b : ctree_supports_asset a
                                           (ctree_of_Block (bh,bd))
                                           (payaddr_addr (stakeaddr bh))).
        { revert H6. apply subqc_supports_asset. exact Lsubqc. }
        generalize (ctree_supports_asset_In_statefun _ _ f _ HTf L2a).
        intros L2a'.
        generalize (ctree_supports_asset_In_statefun _ _ f _ HTf L2b).
        intros L2b'.
        rewrite <- H0 in L2a'.
        destruct a as [h' [obl' u']].
        simpl in H9. rewrite <- H9 in L2b'. rewrite <- H0 in L2b'.
        destruct (Hf2 h (payaddr_addr (stakeaddr bh)) (bday,(None,currency (stake bh))) (payaddr_addr (stakeaddr bh)) (obl',u') L2a' L2b') as [_ H11].
        inversion H11. subst u'.
        unfold asset_value in H8. simpl in H8. discriminate H8.
    - simpl. intros H1. inversion H1.
      + inversion H2.
        assert (L2a : ctree_supports_asset
                        (stakeassetid bh, (bday,(Some(a',n), currency (stake bh)))) 
                        (ctree_of_Block (bh,bd))
                        (payaddr_addr (stakeaddr bh))).
        { revert H4. apply subqc_supports_asset. exact Lsubqc. }
        assert (L2b : ctree_supports_asset a
                                           (ctree_of_Block (bh,bd))
                                           (payaddr_addr (stakeaddr bh))).
        { revert H6. apply subqc_supports_asset. exact Lsubqc. }
        generalize (ctree_supports_asset_In_statefun _ _ f _ HTf L2a).
        intros L2a'.
        generalize (ctree_supports_asset_In_statefun _ _ f _ HTf L2b).
        intros L2b'.
        rewrite <- H0 in L2a'.
        destruct a as [h' [obl' u']].
        simpl in H9. rewrite <- H9 in L2b'. rewrite <- H0 in L2b'.
        destruct (Hf2 h (payaddr_addr (stakeaddr bh)) (bday,(Some(a',n),currency (stake bh))) (payaddr_addr (stakeaddr bh)) (obl',u') L2a' L2b') as [_ H11].
        inversion H11. subst u'.
        unfold asset_value in H8. simpl in H8. inversion H8.
        inversion H3. omega.
      + exfalso.
        assert (L2a : ctree_supports_asset
                        (stakeassetid bh, (bday,(Some(a', n), currency (stake bh))))
                        (ctree_of_Block (bh,bd))
                        (payaddr_addr (stakeaddr bh))).
        { revert H4. apply subqc_supports_asset. exact Lsubqc. }
        assert (L2b : ctree_supports_asset a
                                           (ctree_of_Block (bh,bd))
                                           (payaddr_addr (stakeaddr bh))).
        { revert H6. apply subqc_supports_asset. exact Lsubqc. }
        generalize (ctree_supports_asset_In_statefun _ _ f _ HTf L2a).
        intros L2a'.
        generalize (ctree_supports_asset_In_statefun _ _ f _ HTf L2b).
        intros L2b'.
        rewrite <- H0 in L2a'.
        destruct a as [h' [obl' u']].
        simpl in H9. rewrite <- H9 in L2b'. rewrite <- H0 in L2b'.
        destruct (Hf2 h (payaddr_addr (stakeaddr bh)) (bday,(Some(a',n),currency (stake bh))) (payaddr_addr (stakeaddr bh)) (obl',u') L2a' L2b') as [_ H11].
        inversion H11. subst u'.
        unfold asset_value in H8. simpl in H8. discriminate H8.
  }
  revert H3 H5 L2. clear. intros H3 H5 L2.
  simpl in H5.
  rewrite out_burncost_app.
  omega.
Qed.

Lemma tx_of_Block_supported_lem_2 tht sigt blockheight rew {pbh plr ti} (bh:@BlockHeader pbh plr ti) (bd:BlockDelta) :
  subqc (prevledger bh) (ctree_of_Block (bh, bd)) ->
  ctree_supports_tx tht sigt blockheight (coinstake bh) (prevledger bh) 0
                    (rew + totalfees bh) ->
  (forall tx : Tx,
     In_dom tx (blockdelta_stxl bd) ->
     exists fee : nat,
       ctree_supports_tx tht sigt blockheight tx (ctree_of_Block (bh, bd)) fee 0) ->
  (forall (obl : obligation) gamma (nonce : nat) (d : theoryspec) (alpha : addr),
    In (alpha, (obl, theorypublication gamma nonce d)) (tx_outputs (tx_of_Block (bh, bd))) ->
    check_theoryspec_p d /\
    (exists (beta : addr) (h : hashval) (bday : nat) 
           (obl0 : obligation),
      beta = hashval_publication_addr (hashpair (hashaddr (payaddr_addr gamma)) (hashpair (hashnat nonce) (hashtheoryspec d))) /\
      In (beta, h) (tx_inputs (tx_of_Block (bh, bd))) /\
      bday + intention_minage <= blockheight /\
      ctree_supports_asset (h, (bday, (obl0, marker)))
                           (ctree_of_Block (bh, bd)) beta))
  /\
  (forall (obl : obligation) gamma (nonce : nat) (th:option hashval) (d : signaspec) (alpha : addr),
    In (alpha, (obl, signapublication gamma nonce th d)) (tx_outputs (tx_of_Block (bh, bd))) ->
    check_signaspec_p (ctree_lookup_stp (ctree_of_Block (bh, bd)))
      (ctree_lookup_known (ctree_of_Block (bh, bd))) tht sigt th d /\
    exists (beta : addr) (h : hashval) (bday : nat) 
           (obl0 : obligation),
      beta = hashval_publication_addr (hashpair (hashaddr (payaddr_addr gamma)) (hashpair (hashnat nonce) (hashopair2 th (hashsignaspec d)))) /\
      In (beta, h) (tx_inputs (tx_of_Block (bh, bd))) /\
      bday + intention_minage <= blockheight /\
      ctree_supports_asset (h, (bday, (obl0, marker)))
                           (ctree_of_Block (bh, bd)) beta)
  /\
  (forall (obl : obligation) gamma (nonce : nat) (th:option hashval) (d : doc) (alpha : addr),
    In (alpha, (obl, docpublication gamma nonce th d)) (tx_outputs (tx_of_Block (bh, bd))) ->
    check_doc_p (ctree_lookup_stp (ctree_of_Block (bh, bd)))
      (ctree_lookup_known (ctree_of_Block (bh, bd))) tht sigt th d /\
    exists (beta : addr) (h : hashval) (bday : nat) 
           (obl0 : obligation),
      beta = hashval_publication_addr (hashpair (hashaddr (payaddr_addr gamma)) (hashpair (hashnat nonce) (hashopair2 th (hashdoc d)))) /\
      In (beta, h) (tx_inputs (tx_of_Block (bh, bd))) /\
      bday + intention_minage <= blockheight /\
      ctree_supports_asset (h, (bday, (obl0, marker)))
                           (ctree_of_Block (bh, bd)) beta).
  intros Lsubqc HvBah HvBj. split; [|split].
  - intros obl gamma nonce d alpha H1.
    apply tx_of_Block_output_iff in H1.
    destruct H1 as [H1|[tx' [sl' [H2 H3]]]].
    + destruct HvBah as [_ [_ [_ [[H5a [H5b H5c]] _]]]].
      destruct (H5a obl gamma nonce d alpha H1) as [Hch [beta [h [bday' [obl' [H6 [H7 [H8 H9]]]]]]]].
      split.
      * exact Hch.
      * { exists beta. exists h. exists bday'. exists obl'. repeat split.
          - exact H6.
          - apply tx_of_Block_input_iff.
            left. simpl in H7. destruct H7 as [H7|[]].
            inversion H7. split; reflexivity.
          - exact H8.
          - revert H9. apply subqc_supports_asset. exact Lsubqc.
        }
    + simpl in H2. generalize H2. intros H2a. apply In_In_dom_lem_2 in H2a.
      destruct (HvBj tx' H2a) as [fee [_ [_ [_ [[H5a [H5b H5c]] _]]]]].
      destruct (H5a obl gamma nonce d alpha H3) as [Hch [beta [h [bday' [obl' [H6 [H7 [H8 H9]]]]]]]].
      split.
      * exact Hch.
      * { exists beta. exists h. exists bday'. exists obl'. repeat split.
          - exact H6.
          - apply tx_of_Block_input_iff.
            right. exists tx'. exists sl'. tauto.
          - exact H8.
          - exact H9.
        }
  - intros obl gamma nonce th d alpha H1.
    apply tx_of_Block_output_iff in H1.
    destruct H1 as [H1|[tx' [sl' [H2 H3]]]].
    + destruct HvBah as [_ [_ [_ [[H5a [H5b H5c]] _]]]].
      destruct (H5b obl gamma nonce th d alpha H1) as [Hch [beta [h [bday' [obl' [H6 [H7 [H8 H9]]]]]]]].
      split.
      * revert Lsubqc Hch. apply subqc_check_signaspec_p.
      * { exists beta. exists h. exists bday'. exists obl'. repeat split.
          - exact H6.
          - apply tx_of_Block_input_iff.
            left. simpl in H7. destruct H7 as [H7|[]].
            inversion H7. split; reflexivity.
          - exact H8.
          - revert H9. apply subqc_supports_asset. exact Lsubqc.
        }
    + simpl in H2. generalize H2. intros H2a. apply In_In_dom_lem_2 in H2a.
      destruct (HvBj tx' H2a) as [fee [_ [_ [_ [[H5a [H5b H5c]] _]]]]].
      destruct (H5b obl gamma nonce th d alpha H3) as [Hch [beta [h [bday' [obl' [H6 [H7 [H8 H9]]]]]]]].
      split.
      * exact Hch.
      * { exists beta. exists h. exists bday'. exists obl'. repeat split.
          - exact H6.
          - apply tx_of_Block_input_iff.
            right. exists tx'. exists sl'. tauto.
          - exact H8.
          - exact H9.
        }
  - intros obl gamma nonce th d alpha H1.
    apply tx_of_Block_output_iff in H1.
    destruct H1 as [H1|[tx' [sl' [H2 H3]]]].
    + destruct HvBah as [_ [_ [_ [[H5a [H5b H5c]] _]]]].
      destruct (H5c obl gamma nonce th d alpha H1) as [Hch [beta [h [bday' [obl' [H6 [H7 [H8 H9]]]]]]]].
      split.
      * revert Lsubqc Hch. apply subqc_check_doc_p.
      * { exists beta. exists h. exists bday'. exists obl'. repeat split.
          - exact H6.
          - apply tx_of_Block_input_iff.
            left. simpl in H7. destruct H7 as [H7|[]].
            inversion H7. split; reflexivity.
          - exact H8.
          - revert H9. apply subqc_supports_asset. exact Lsubqc.
        }
    + simpl in H2. generalize H2. intros H2a. apply In_In_dom_lem_2 in H2a.
      destruct (HvBj tx' H2a) as [fee [_ [_ [_ [[H5a [H5b H5c]] _]]]]].
      destruct (H5c obl gamma nonce th d alpha H3) as [Hch [beta [h [bday' [obl' [H6 [H7 [H8 H9]]]]]]]].
      split.
      * exact Hch.
      * { exists beta. exists h. exists bday'. exists obl'. repeat split.
          - exact H6.
          - apply tx_of_Block_input_iff.
            right. exists tx'. exists sl'. tauto.
          - exact H8.
          - exact H9.
        }
Qed.

Opaque ctree_full_approx_addr.

Theorem tx_of_Block_supported tht sigt blockheight rew check_hit targetf {pbh plr ti} (b:@Block pbh plr ti) :
  ctree_valid (ctree_of_Block b) ->
  valid_Block tht sigt blockheight rew check_hit targetf b ->
  ctree_supports_tx tht sigt blockheight (tx_of_Block b) (ctree_of_Block b) 0 rew.
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
                                     ((payaddr_addr (stakeaddr bh), stakeassetid bh)
                                        :: sTxs_allinputs (blockdelta_stxl bd))
                                     (stake bh + utot)).
        destruct HvBae as [[bday [H4 H5]]|[bday [a [n [H4 [H5a H5]]]]]].
        - apply ctree_asset_value_in_cons with (a := (stakeassetid bh,(bday,(None,currency (stake bh))))).
          + exact H2.
          + revert H4. apply subqc_supports_asset. exact Lsubqc.
          + reflexivity.
          + reflexivity.
        - apply ctree_asset_value_in_cons with (a := (stakeassetid bh,(bday,(Some(a,n),currency (stake bh))))).
          + exact H2.
          + revert H4. apply subqc_supports_asset. exact Lsubqc.
          + reflexivity.
          + reflexivity.
      }
    * revert HT Lsubqc HvBae HvBah H3.
      apply tx_of_Block_supported_lem_1.
  + split.
    * { split.
        - intros alpha b H1.
          destruct H1 as [H1|[beta2 [obl2 [n2 H1]]]].
          + apply tx_of_Block_output_uses_iff in H1.
            destruct H1 as [H1|[tx [sli [slo [H1 H2]]]]].
            * { assert (L3: rights_mentioned alpha b (tx_outputs (coinstake bh))).
                { now left. }
                destruct (HvBah4a alpha b L3) as [H4 [H5 H6]].
                split.
                - revert H4. apply subqc_full_approx_addr. exact Lsubqc.
                - split.
                  + intros [h' [bday' [obl' [beta' H7]]]].
                    apply H5. exists h'. exists bday'. exists obl'. exists beta'.
                    revert H4 H7. apply subqc_full_approx_supports_asset_conv.
                    exact Lsubqc.
                  + change (ctree_rights_balanced (ctree_of_Block (bh, bd)) alpha b
                                                  (((payaddr_addr (stakeaddr bh), stakeassetid bh) ::nil) ++ sTxs_allinputs (blockdelta_stxl bd))
                                                  (stakeoutput bh ++ sTxs_alloutputs (blockdelta_stxl bd))).
                    apply ctree_rights_balanced_app.
                    * { intros rtot1 rtot2 h bday obl beta u H7 H8 H9.
                        assert (L8: ctree_supports_asset (h, (bday,(obl, owns b beta (Some u)))) (prevledger bh) (termaddr_addr alpha)).
                        { revert Lsubqc H4 H8. apply subqc_full_approx_supports_asset_conv. }
                        destruct (H6 rtot1 rtot2 h bday obl beta u H7 L8 H9) as [rtot3 [rtot4 [H10 [H11 H12]]]].
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
                        - intros rtot1 rtot2 h bday obl beta u H9 H10 H11.
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
                                assert (L9: exists bdayoblu : nat * (obligation * preasset),
                                              ctree_supports_asset (h, bdayoblu) (ctree_of_Block (bh, bd)) gamma).
                                { apply Hc1. now left. }
                                destruct L9 as [[bday [obl u]] L9a].
                                apply ctree_rights_consumed_skip with (bday := bday) (obl := obl) (u := u).
                                - apply IH.
                                  + intros delta k H9. apply Hc1. now right.
                                  + intros delta c beta k bday' obl' n H9. apply H8b. now right.
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
                                                  (((payaddr_addr (stakeaddr bh), stakeassetid bh) ::nil) ++ sTxs_allinputs (blockdelta_stxl bd))
                                                  (stakeoutput bh ++ sTxs_alloutputs (blockdelta_stxl bd))).
                    apply ctree_rights_balanced_app.
                    * { intros rtot1 rtot2 h bday obl beta u H7 H8 H9.
                        destruct (rights_mentioned_dec alpha b (tx_outputs (coinstake bh))) as [D1|D1].
                        - destruct (HvBah4a alpha b D1) as [H4' [H5' H6']].
                          assert (L8: ctree_supports_asset (h, (bday,(obl, owns b beta (Some u)))) (prevledger bh) (termaddr_addr alpha)).
                          { revert Lsubqc H4' H8. apply subqc_full_approx_supports_asset_conv. }
                          destruct (H6' rtot1 rtot2 h bday obl beta u H7 L8 H9) as [rtot3 [rtot4 [H10 [H11 H12]]]].
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
                          + destruct HvBae as [[bday' [H10 _]]|[bday' [a' [n [H10 _]]]]].
                            * assert (L10: ctree_supports_asset
                                             (stakeassetid bh, (bday',(None, currency (stake bh))))
                                             (ctree_of_Block (bh,bd)) (payaddr_addr (stakeaddr bh))).
                              { revert Lsubqc H10. apply subqc_supports_asset. }
                              assert (L11: ~exists r2, currency (stake bh) = rights b r2 alpha).
                              { intros [r2 H11]. discriminate H11. }
                              revert L10 L11. apply ctree_rights_consumed_skip.
                              apply ctree_rights_consumed_nil.
                            * assert (L10: ctree_supports_asset
                                             (stakeassetid bh, (bday', (Some(a', n), currency (stake bh))))
                                             (ctree_of_Block (bh,bd)) (payaddr_addr (stakeaddr bh))).
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
                        - intros rtot1 rtot2 h bday obl beta u H9 H10 H11.
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
                                assert (L9: exists bdayoblu : nat * (obligation * preasset),
                                              ctree_supports_asset (h, bdayoblu) (ctree_of_Block (bh, bd)) gamma).
                                { apply Hc1'. now left. }
                                destruct L9 as [[bday [obl u]] L9a].
                                apply ctree_rights_consumed_skip with (bday := bday) (obl := obl) (u := u).
                                - apply IH.
                                  + intros delta k H9. apply Hc1'. now right.
                                  + intros delta c beta k bday' obl' n H9. apply H8b'. now right.
                                - exact L9a.
                                - intros [r2 H10]. subst u.
                                  apply D1'. revert L9a. apply H8b'.
                                  now left.
                              }
                          + omega.
                      }
              }
          + apply tx_of_Block_output_iff in H1.
            destruct H1 as [H1|[tx [[sli slo] [H1 H2]]]].
            * { assert (L3: rights_mentioned alpha b (tx_outputs (coinstake bh))).
                { right. exists beta2. exists obl2. exists n2. exact H1. }
                destruct (HvBah4a alpha b L3) as [H4 [H5 H6]].
                split.
                - revert H4. apply subqc_full_approx_addr. exact Lsubqc.
                - split.
                  + intros [h' [bday' [obl' [beta' H7]]]].
                    apply H5. exists h'. exists bday'. exists obl'. exists beta'.
                    revert H4 H7. apply subqc_full_approx_supports_asset_conv.
                    exact Lsubqc.
                  + change (ctree_rights_balanced (ctree_of_Block (bh, bd)) alpha b
                                                  (((payaddr_addr (stakeaddr bh), stakeassetid bh) ::nil) ++ sTxs_allinputs (blockdelta_stxl bd))
                                                  (stakeoutput bh ++ sTxs_alloutputs (blockdelta_stxl bd))).
                    apply ctree_rights_balanced_app.
                    * { intros rtot1 rtot2 h bday obl beta u H7 H8 H9.
                        assert (L8: ctree_supports_asset (h, (bday,(obl, owns b beta (Some u)))) (prevledger bh) (termaddr_addr alpha)).
                        { revert Lsubqc H4 H8. apply subqc_full_approx_supports_asset_conv. }
                        destruct (H6 rtot1 rtot2 h bday obl beta u H7 L8 H9) as [rtot3 [rtot4 [H10 [H11 H12]]]].
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
                        - intros rtot1 rtot2 h bday obl beta u H9 H10 H11.
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
                                assert (L9: exists bdayoblu : nat * (obligation * preasset),
                                              ctree_supports_asset (h, bdayoblu) (ctree_of_Block (bh, bd)) gamma).
                                { apply Hc1. now left. }
                                destruct L9 as [[bday [obl u]] L9a].
                                apply ctree_rights_consumed_skip with (bday := bday) (obl := obl) (u := u).
                                - apply IH.
                                  + intros delta k H9. apply Hc1. now right.
                                  + intros delta c beta k bday' obl' n H9. apply H8b. now right.
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
                                                  (((payaddr_addr (stakeaddr bh), stakeassetid bh) ::nil) ++ sTxs_allinputs (blockdelta_stxl bd))
                                                  (stakeoutput bh ++ sTxs_alloutputs (blockdelta_stxl bd))).
                    apply ctree_rights_balanced_app.
                    * { intros rtot1 rtot2 h bday obl beta u H7 H8 H9.
                        destruct (rights_mentioned_dec alpha b (tx_outputs (coinstake bh))) as [D1|D1].
                        - destruct (HvBah4a alpha b D1) as [H4' [H5' H6']].
                          assert (L8: ctree_supports_asset (h, (bday, (obl, owns b beta (Some u)))) (prevledger bh) (termaddr_addr alpha)).
                          { revert Lsubqc H4' H8. apply subqc_full_approx_supports_asset_conv. }
                          destruct (H6' rtot1 rtot2 h bday obl beta u H7 L8 H9) as [rtot3 [rtot4 [H10 [H11 H12]]]].
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
                          + destruct HvBae as [[bday' [H10 _]]|[bday' [a' [n [H10 _]]]]].
                            * assert (L10: ctree_supports_asset
                                             (stakeassetid bh, (bday', (None, currency (stake bh))))
                                             (ctree_of_Block (bh,bd)) (payaddr_addr (stakeaddr bh))).
                              { revert Lsubqc H10. apply subqc_supports_asset. }
                              assert (L11: ~exists r2, currency (stake bh) = rights b r2 alpha).
                              { intros [r2 H11]. discriminate H11. }
                              revert L10 L11. apply ctree_rights_consumed_skip.
                              apply ctree_rights_consumed_nil.
                            * assert (L10: ctree_supports_asset
                                             (stakeassetid bh, (bday', (Some(a', n), currency (stake bh))))
                                             (ctree_of_Block (bh,bd)) (payaddr_addr (stakeaddr bh))).
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
                        - intros rtot1 rtot2 h bday obl beta u H9 H10 H11.
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
                                assert (L9: exists bdayoblu : nat * (obligation * preasset),
                                              ctree_supports_asset (h, bdayoblu) (ctree_of_Block (bh, bd)) gamma).
                                { apply Hc1'. now left. }
                                destruct L9 as [[bday [obl u]] L9a].
                                apply ctree_rights_consumed_skip with (bday := bday) (obl := obl) (u := u).
                                - apply IH.
                                  + intros delta k H9. apply Hc1'. now right.
                                  + intros delta c beta k bday' obl' n H9. apply H8b'. now right.
                                - exact L9a.
                                - intros [r2 H10]. subst u.
                                  apply D1'. revert L9a. apply H8b'.
                                  now left.
                              }
                          + omega.
                      }
              }
        - intros alpha b beta h bday obl n H1 H2.
          apply tx_of_Block_input_iff in H1.
          destruct H1 as [[H1a H1b]|[tx [[sli slo] [H1a H1b]]]].
          + exfalso. (*** impossible since the stake asset is currency, not rights. ***)
            generalize HT. intros [f [[_ [Hf2 _]] HTf]].
            generalize (ctree_supports_asset_In_statefun _ _ f _ HTf H2).
            intros H3.
            destruct HvBae as [[bday' [H4 H5]]|[bday' [a' [n' [H4 [H5a H5]]]]]].
            * assert (L4: ctree_supports_asset
                            (h, (bday',(None, currency (stake bh))))
                            (ctree_of_Block (bh,bd)) (payaddr_addr (stakeaddr bh))).
              { simpl in H1b. rewrite H1b.
                revert Lsubqc H4. apply subqc_supports_asset.
              }
              generalize (ctree_supports_asset_In_statefun _ _ f _ HTf L4).
              intros L4a.
              destruct (Hf2 h _ _ _ _ H3 L4a) as [_ H6].
              discriminate H6.
            * assert (L4: ctree_supports_asset
                            (h, (bday',((Some(a', n')), currency (stake bh))))
                            (ctree_of_Block (bh,bd)) (payaddr_addr (stakeaddr bh))).
              { simpl in H1b. rewrite H1b.
                revert Lsubqc H4. apply subqc_supports_asset.
              }
              generalize (ctree_supports_asset_In_statefun _ _ f _ HTf L4).
              intros L4a.
              destruct (Hf2 h _ _ _ _ H3 L4a) as [_ H6].
              discriminate H6.
          + generalize H1a. intros H1aa. apply In_In_dom_lem_2 in H1aa.
            destruct (HvBj tx H1aa) as [fee [_ [_ [[_ H4b] _]]]].
            destruct (H4b _ _ _ _ _ _ _ H1b H2) as [H5|[gamma [obl2 [n2 H5]]]].
            * left. apply tx_of_Block_output_uses_iff.
              right. exists tx. exists sli. exists slo. split; assumption.
            * right. exists gamma. exists obl2. exists n2.
              apply tx_of_Block_output_iff.
              right. exists tx. exists (sli,slo). split; assumption.
      }
    * { split.
        - revert Lsubqc HvBah HvBj.
          apply tx_of_Block_supported_lem_2.
        - split.
          + revert Lsubqc HvBah6 HvBj. clear.
            intros Lsubqc HvBah6 HvBj.
            intros alpha b obl beta r H1.
            apply tx_of_Block_output_iff in H1.
            destruct H1 as [H1|[tx [[sli slo] [H1 H2]]]].
            * { destruct (HvBah6 alpha b obl beta r H1) as [H7 H8].
                split.
                - revert H7. apply subqc_full_approx_addr. exact Lsubqc.
                - destruct H8 as [[h [beta' [bday' [obl' [r' [H9 H10]]]]]]|[H9 H10]].
                  + left. exists h. exists beta'. exists bday'. exists obl'. exists r'.
                    split.
                    * revert H9. apply subqc_supports_asset. exact Lsubqc.
                    * apply tx_of_Block_input_iff.
                      left. simpl in H10. destruct H10 as [H10|[]].
                      inversion H10.
                  + right. split.
                    * intros [h [beta' [bday' [obl' [r' H11]]]]].
                      apply H9.
                      exists h. exists beta'. exists bday'. exists obl'. exists r'.
                      revert Lsubqc H7 H11.
                      apply subqc_full_approx_supports_asset_conv.
                    * { destruct H10 as [k1 [k2 [H10a H10b]]].
                        exists k1. exists k2. split.
                        - apply tx_of_Block_output_creates_iff.
                          left. exact H10a.
                        - exact H10b.
                      }
              }
            * { generalize H1. intros H1b. apply In_In_dom_lem_2 in H1b.
                destruct (HvBj tx H1b) as [fee [_ [_ [_ [_ [H6 _]]]]]].
                destruct (H6 alpha b obl beta r H2) as [H7 H8].
                split.
                - exact H7.
                - destruct H8 as [[h [beta' [bday' [obl' [r' [H9 H10]]]]]]|[H9 H10]].
                  + left. exists h. exists beta'. exists bday'. exists obl'. exists r'.
                    split.
                    * exact H9.
                    * apply tx_of_Block_input_iff. right. exists tx. exists (sli,slo).
                      split; assumption.
                  + right. split.
                    * intros [h [beta' [bday' [obl' [r' H11]]]]].
                      apply H9.
                      exists h. exists beta'. exists bday'. exists obl'. exists r'.
                      exact H11.
                    * { destruct H10 as [k1 [k2 [H10a H10b]]].
                        exists k1. exists k2. split.
                        - apply tx_of_Block_output_creates_iff.
                          right. exists tx. exists sli. exists slo. split.
                          + exact H1.
                          + exact H10a.
                        - exact H10b.
                      }
              }
          + split.
            * { intros k1 k2 b H1.
                apply tx_of_Block_output_creates_iff in H1.
                destruct H1 as [H1|[tx [sli [slo [H1 H2]]]]].
                - destruct (HvBah7 k1 k2 b H1) as [H3 H4].
                  split.
                  + revert Lsubqc H3. apply subqc_full_approx_addr.
                  + intros H5.
                    assert (L4: ~ (exists (h' : hashval) (beta' : payaddr) (bday':nat) (obl' : obligation) (r' : option nat),
                                     ctree_supports_asset (h', (bday', (obl', owns b beta' r')))
                                                          (prevledger bh) (hashval_term_addr k1))).
                    { intros [h' [beta' [bday' [obl' [r' H6]]]]].
                      apply H5. exists h'. exists beta'. exists bday'. exists obl'. exists r'.
                      revert Lsubqc H6. apply subqc_supports_asset.
                    }
                    destruct (H4 L4) as [[beta [obl [r H6]]] H7].
                    split.
                    * exists beta. exists obl. exists r.
                      apply tx_of_Block_output_iff.
                      left. exact H6.
                    * { destruct b.
                        - destruct H7 as [obl2 [obl3 [H8 H9]]].
                          exists obl2. exists obl3. split.
                          + apply tx_of_Block_output_iff.
                            left. exact H8.
                          + apply tx_of_Block_output_iff.
                            left. exact H9.
                        - destruct H7 as [obl2 H8].
                          exists obl2. 
                          apply tx_of_Block_output_iff.
                          left. exact H8.
                      }
                - generalize H1. intros H1b. apply In_In_dom_lem_2 in H1b.
                  destruct (HvBj tx H1b) as [fee [_ [_ [_ [_ [_ [H7 _]]]]]]].
                  destruct (H7 k1 k2 b H2) as [H3 H4].
                  split.
                  + exact H3.
                  + intros H5.
                    assert (L4: ~ (exists (h' : hashval) (beta' : payaddr) (bday' : nat) (obl' : obligation) (r' : option nat),
                                     ctree_supports_asset (h', (bday', (obl', owns b beta' r')))
                                                          (ctree_of_Block (bh, bd)) (hashval_term_addr k1))).
                    { intros [h' [beta' [bday' [obl' [r' H6]]]]].
                      apply H5. exists h'. exists beta'. exists bday'. exists obl'. exists r'.
                      exact H6.
                    }
                    destruct (H4 L4) as [[beta [obl [r H6]]] H8].
                    split.
                    * exists beta. exists obl. exists r.
                      apply tx_of_Block_output_iff.
                      right. exists tx. exists (sli,slo). split; assumption.
                    * { destruct b.
                        - destruct H8 as [obl2 [obl3 [H8 H9]]].
                          exists obl2. exists obl3. split.
                          + apply tx_of_Block_output_iff.
                            right. exists tx. exists (sli,slo). split.
                            * exact H1.
                            * exact H8.
                          + apply tx_of_Block_output_iff.
                            right. exists tx. exists (sli,slo). split.
                            * exact H1.
                            * exact H9.
                        - destruct H8 as [obl2 H8].
                          exists obl2. 
                          apply tx_of_Block_output_iff.
                          right. exists tx. exists (sli,slo). split.
                          + exact H1.
                          + exact H8.
                      }
              }
            * { intros alpha h bday obl u H1 H2.
                apply tx_of_Block_input_iff in H1.
                destruct H1 as [[H1a H1b]|[tx [sl [H1a H1b]]]].
                - exfalso.
                  (*** This seemed to be a problematic case, but it's actually impossible.
                       It assumes the stakeassetid is for a bounty, but we know it's for currency. ***)
                  generalize HT. intros [f [[_ [Hf2 _]] HTf]].
                  generalize (ctree_supports_asset_In_statefun _ _ f _ HTf H2).
                  intros H3.
                  destruct HvBae as [[bday' [H4 H5]]|[bday' [a' [n [H4 H5]]]]].
                  + assert (L4: ctree_supports_asset
                                  (h, (bday', (None, currency (stake bh))))
                                  (ctree_of_Block (bh,bd)) (payaddr_addr (stakeaddr bh))).
                    { rewrite H1b.
                      revert Lsubqc H4. apply subqc_supports_asset.
                    }
                    generalize (ctree_supports_asset_In_statefun _ _ f _ HTf L4).
                    intros L4a.
                    destruct (Hf2 h _ _ _ _ H3 L4a) as [_ H6].
                    discriminate H6.
                  + assert (L4: ctree_supports_asset
                                  (h, (bday', ((Some(a', n)), currency (stake bh))))
                                  (ctree_of_Block (bh,bd)) (payaddr_addr (stakeaddr bh))).
                    { rewrite H1b.
                      revert Lsubqc H4. apply subqc_supports_asset.
                    }
                    generalize (ctree_supports_asset_In_statefun _ _ f _ HTf L4).
                    intros L4a.
                    destruct (Hf2 h _ _ _ _ H3 L4a) as [_ H6].
                    discriminate H6.
                - generalize H1a. intros H1ab. apply In_In_dom_lem_2 in H1ab.
                  destruct (HvBj tx H1ab) as [fee [_ [_ [_ [_ [_ [_ H8]]]]]]].
                  destruct (H8 alpha h bday obl u H1b H2) as [H3 [h' [bday' [obl' [beta' [u' [H4 [H5 H6]]]]]]]].
                  split.
                  + exact H3.
                  + exists h'. exists bday'. exists obl'. exists beta'. exists u'. repeat split.
                    * apply tx_of_Block_input_iff. right. exists tx. exists sl.
                      split; assumption.
                    * exact H5.
                    * apply tx_of_Block_output_iff. right. exists tx. exists sl.
                      split; assumption.
              }
      }
Qed.

Definition ledgerroot_valid (h:hashval) : Prop :=
  exists (tht:option (ttree 160)) (sigt:option (stree 160)) (k:hashval),
    h = hashopair2 (ottree_hashroot tht) (hashopair2 (ostree_hashroot sigt) k) (*** [+] ***)
    /\
    ctree_valid (ctreeH 162 k).

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

Lemma endledgerroot_plr_valid_lem1 pbh lroot lr ti (bh:@BlockHeader pbh lroot ti) bd (f:statefun) :
  mtree_approx_fun_p (ctree_mtree (ctreeH 162 lr)) f ->
  ctree_hashroot (prevledger bh) = lr ->
  cgraft_valid (prevledgergraft bd) ->
  mtree_approx_fun_p (ctree_mtree (ctree_of_Block (bh, bd))) f.
intros H1 H2 H3.
apply (mtree_hashroot_mtree_approx_fun_p (ctree_mtree (ctreeH 162 lr))).
- change (mtree_hashroot (ctree_mtree (ctreeH 162 lr)) =
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
- intros [tht [sigt H2]]. generalize H2. intros [[H2aa [H2ab [H2ac [H2ad [H2ae [H2af [H2ag H2ah]]]]]]] [H2b [H2c [H2d [H2e [H2f [H2g [H2h [H2i [H2j [H2k H2l]]]]]]]]]]].
  assert (LT: ctree_valid (ctree_of_Block (bh,bd))).
  { unfold ctree_of_Block. apply ctree_valid_cgraft_valid.
    - revert H1. unfold ledgerroot_valid. unfold ctree_valid.
      intros [tht' [sigt' [k [E1 H3]]]].
      revert H3. apply mtree_hashroot_eq_valid.
      rewrite mtree_hashroot_ctree_hashroot.
      rewrite mtree_hashroot_ctree_hashroot.
      rewrite ctree_hashroot_ctree_H.
      f_equal. 
      assert (L1: hashopair2 (ottree_hashroot tht) (hashopair2 (ostree_hashroot sigt) (ctree_hashroot (prevledger bh)))
                  =
                  (hashopair2 (ottree_hashroot tht') (hashopair2 (ostree_hashroot sigt') k))) by congruence.
      apply hashopair2inj in L1.
      destruct L1 as [_ H4].
      apply hashopair2inj in H4.
      destruct H4 as [_ H4].
      exact H4.
    - exact H2i.
  }
  destruct H2l as [T [H2la H2lb]].
  change (ledgerroot_valid (newledgerroot bh)).
  rewrite H2la.
  unfold ledgerroot_valid.
  unfold ctree_valid.
  exists (tx_update_ottree (tx_of_Block (bh, bd)) tht). exists (tx_update_ostree (tx_of_Block (bh, bd)) sigt). exists (ctree_hashroot T).
  split; try reflexivity.
  assert (L1: octree_supports_tx tht sigt 0 (tx_of_Block (bh,bd)) (Some (ctree_of_Block (bh,bd))) 0 (rewfn 0)).
  { exact (tx_of_Block_supported tht sigt 0 (rewfn 0) check_hit targetf (bh,bd) LT H2). }
  apply (mtree_hashroot_eq_valid (ctree_mtree T)).
  + rewrite mtree_hashroot_ctree_hashroot.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite ctree_hashroot_ctree_H.
    reflexivity.
  + destruct H1 as [tht' [sigt' [k [E1 [f [H1a H1b]]]]]].
    assert (Lk : ctree_hashroot (prevledger bh) = k).
    { assert (Ek : hashopair2 (ottree_hashroot tht) (hashopair2 (ostree_hashroot sigt) (ctree_hashroot (prevledger bh))) = hashopair2 (ottree_hashroot tht') (hashopair2 (ostree_hashroot sigt') k)) by congruence.
      apply hashopair2inj in Ek.
      destruct Ek as [_ Ek].
      apply hashopair2inj in Ek.
      destruct Ek as [_ Ek].
      exact Ek.
    }
    assert (LTf: octree_approx_fun_p (Some (ctree_of_Block (bh,bd))) f).
    { exact (endledgerroot_plr_valid_lem1 None genlr k ti bh bd f H1b Lk H2i). }
    exists (tx_statefun_trans 0 (tx_of_Block (bh,bd)) f). split.
    * { apply sf_tx_valid_thm with (tht := tht) (sigt := sigt) (bday := 0) (fee := 0) (rew := (rewfn 0)).
        - exact H1a.
        - revert H2. apply tx_of_Block_valid.
        - assert (L2: mtree_supports_tx tht sigt 0 (tx_of_Block (bh, bd))
                                        (octree_mtree (Some (ctree_of_Block (bh, bd)))) 0 
                                        (rewfn 0)).
          { revert L1. apply octree_mtree_supports_tx. }
          apply mtree_supports_tx_statefun with (f := f) in L2.
          + exact L2.
          + destruct H1a as [_ [Hf2 _]]. exact Hf2.
          + unfold octree_approx_fun_p in LTf.
            exact LTf.
      }
    * { assert (L4: mtree_approx_fun_p (octree_mtree (Some T)) (tx_statefun_trans 0 (tx_of_Block (bh, bd)) f)).
        { rewrite <- H2lb.
          set (tx' := (tx_of_Block (bh,bd))).
          set (T' := (ctree_of_Block (bh,bd))).
          assert (L5: octree_approx_fun_p (tx_octree_trans 0 tx' (Some T')) (tx_statefun_trans 0 tx' f)).
          { apply (octree_approx_trans tht sigt 0 tx' (Some T') f 0 (rewfn 0)).
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
- intros [H3 [tht [sigt H2]]].
  generalize H2.
  intros [[H2aa [H2ab [H2ac [H2ad [H2ae [H2af [H2ag H2ah]]]]]]] [H2b [H2c [H2d [H2e [H2f [H2g [H2h [H2i [H2j [H2k H2l]]]]]]]]]]].
  assert (LT: ctree_valid (ctree_of_Block (bh,bd))).
  { unfold ctree_of_Block. apply ctree_valid_cgraft_valid.
    - generalize (IH H3). unfold ledgerroot_valid. unfold ctree_valid.
      intros [tht' [sigt' [k [H3a H3b]]]].
      revert H3b.
      apply mtree_hashroot_eq_valid.
      rewrite mtree_hashroot_ctree_hashroot.
      rewrite mtree_hashroot_ctree_hashroot.
      rewrite ctree_hashroot_ctree_H. f_equal.
      assert (Ek : hashopair2 (ottree_hashroot tht) (hashopair2 (ostree_hashroot sigt) (ctree_hashroot (prevledger bh))) = hashopair2 (ottree_hashroot tht') (hashopair2 (ostree_hashroot sigt') k)) by congruence.
      apply hashopair2inj in Ek.
      destruct Ek as [_ Ek].
      apply hashopair2inj in Ek.
      destruct Ek as [_ Ek].
      exact Ek.
    - exact H2i.
  }
  destruct H2l as [T [H2la H2lb]].
  change (ledgerroot_valid (newledgerroot bh)).
  rewrite H2la.
  unfold ledgerroot_valid.
  unfold ctree_valid.
  assert (L1: octree_supports_tx tht sigt (S n) (tx_of_Block (bh,bd)) (Some (ctree_of_Block (bh,bd))) 0 (rewfn (S n))).
  { exact (tx_of_Block_supported tht sigt (S n) (rewfn (S n)) check_hit targetf (bh,bd) LT H2). }
  exists (tx_update_ottree (tx_of_Block (bh, bd)) tht).
  exists (tx_update_ostree (tx_of_Block (bh, bd)) sigt).
  exists (ctree_hashroot T).
  split; try reflexivity.
  apply (mtree_hashroot_eq_valid (ctree_mtree T)).
  + rewrite mtree_hashroot_ctree_hashroot.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite ctree_hashroot_ctree_H.
    reflexivity.
  + destruct (IH H3) as [tht' [sigt' [k [H1a [f [H1b H1c]]]]]].
    assert (Lk : ctree_hashroot (prevledger bh) = k).
    { assert (Ek : hashopair2 (ottree_hashroot tht) (hashopair2 (ostree_hashroot sigt) (ctree_hashroot (prevledger bh))) = hashopair2 (ottree_hashroot tht') (hashopair2 (ostree_hashroot sigt') k)) by congruence.
      apply hashopair2inj in Ek.
      destruct Ek as [_ Ek].
      apply hashopair2inj in Ek.
      destruct Ek as [_ Ek].
      exact Ek.
    }
    assert (LTf: octree_approx_fun_p (Some (ctree_of_Block (bh,bd))) f).
    { exact (endledgerroot_plr_valid_lem1 _ _ k ti bh bd f H1c Lk H2i). }
    exists (tx_statefun_trans (S n) (tx_of_Block (bh,bd)) f). split.
    * { apply sf_tx_valid_thm with (tht := tht) (sigt := sigt) (bday := (S n)) (fee := 0) (rew := (rewfn (S n))).
        - exact H1b.
        - revert H2. apply tx_of_Block_valid.
        - assert (L2: mtree_supports_tx tht sigt (S n) (tx_of_Block (bh, bd))
                                        (octree_mtree (Some (ctree_of_Block (bh, bd)))) 0 
                                        (rewfn (S n))).
          { revert L1. apply octree_mtree_supports_tx. }
          apply mtree_supports_tx_statefun with (f := f) in L2.
          + exact L2.
          + destruct H1b as [_ [Hf2 _]]. exact Hf2.
          + unfold octree_approx_fun_p in LTf.
            exact LTf.
      }
    * { assert (L4: mtree_approx_fun_p (octree_mtree (Some T)) (tx_statefun_trans (S n) (tx_of_Block (bh, bd)) f)).
        { rewrite <- H2lb.
          set (tx' := (tx_of_Block (bh,bd))).
          set (T' := (ctree_of_Block (bh,bd))).
          assert (L5: octree_approx_fun_p (tx_octree_trans (S n) tx' (Some T')) (tx_statefun_trans (S n) tx' f)).
          { apply (octree_approx_trans tht sigt (S n) tx' (Some T') f 0 (rewfn (S n))).
            - exact H1b.
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

Theorem endledgerroot_plr_sum_bdd (tht tht2:option (ttree 160)) (sigt sigt2:option (stree 160)) k k2 initdistr al bl rewfn check_hit targetf {genlr pbh plr ti n}
      (bc : @BlockChain genlr pbh plr ti n) :
  hashopair2 (ottree_hashroot tht) (hashopair2 (ostree_hashroot sigt) k) = genlr ->
  ctree_valid (ctreeH 162 k) ->
  octree_totalassets (Some (ctreeH 162 k)) al ->
  asset_value_sum al = initdistr ->
  valid_BlockChain rewfn check_hit targetf bc ->
  hashopair2 (ottree_hashroot tht2) (hashopair2 (ostree_hashroot sigt2) k2) = plr ->
  octree_totalassets (Some (ctreeH 162 k2)) bl ->
  asset_value_sum bl <= units_as_of_block initdistr rewfn (S n).
intros H0 H1 H2 H3. revert tht2 sigt2 k2 bl.
induction bc as [ti [bh bd]|pbh plr ti n bc IH [bh bd]].
- intros tht2 sigt2 k2 bl [tht' [sigt' H4]] H5a H5b.
  simpl. unfold valid_BlockChain in H4.
  generalize H4.
  intros [[H4aa [H4ab [H4ac [H4ad [H4ae [H4af [H4ag H4ah]]]]]]] [H4b [H4c [H4d [H4e [H4f [H4g [H4h [H4i [H4j [H4k [T [HT1 HT2]]]]]]]]]]]]].
  assert (L0: hashopair2 (ottree_hashroot tht) (hashopair2 (ostree_hashroot sigt) (ctree_hashroot (ctree_of_Block(bh,bd)))) = genlr). (*** [+] ***)
  { transitivity (hashopair2 (ottree_hashroot tht) (hashopair2 (ostree_hashroot sigt) (ctree_hashroot (prevledger bh)))).
    - f_equal. f_equal. unfold ctree_of_Block. symmetry.
      apply subqc_hashroot_eq. apply ctree_cgraft_subqc. exact H4i.
    - rewrite <- H0. f_equal. f_equal.
      rewrite <- H4ad in H0.
      apply hashopair2inj in H0. destruct H0 as [_ H0].
      apply hashopair2inj in H0. destruct H0 as [_ H0].
      symmetry. exact H0.
  }
  assert (L1: octree_valid (Some (ctree_of_Block (bh, bd)))).
  { unfold octree_valid. revert H1.
    unfold ctree_valid.
    apply mtree_hashroot_eq_valid.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite ctree_hashroot_ctree_H.
    f_equal.
    rewrite <- H0 in L0.
    apply hashopair2inj in L0. destruct L0 as [_ L0].
    apply hashopair2inj in L0. destruct L0 as [_ L0].
    exact L0.
  }
  assert (L2: tx_valid (tx_of_Block (bh, bd))).
  { revert H4. apply tx_of_Block_valid. }
  assert (L3: octree_supports_tx tht' sigt' 0 (tx_of_Block (bh, bd)) (Some (ctree_of_Block (bh, bd))) 0 (rewfn 0)).
  { unfold octree_supports_tx. revert L1 H4. unfold octree_valid. apply tx_of_Block_supported. }
  generalize L1. intros [f [Hf HTf]].
  assert (L4: mtree_approx_fun_p (ctree_mtree (ctreeH 162 k)) f).
  { revert HTf. apply mtree_hashroot_mtree_approx_fun_p.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite ctree_hashroot_ctree_H.
    f_equal.
    rewrite <- H0 in L0.
    apply hashopair2inj in L0. destruct L0 as [_ L0].
    apply hashopair2inj in L0. destruct L0 as [_ L0].
    exact L0.
  }
  assert (L5: octree_totalassets (Some (ctree_of_Block (bh, bd))) al).
  { unfold octree_totalassets. unfold octree_mtree.
    apply (mtree_approx_fun_p_totalassets _ _ _ HTf).
    revert H2. unfold octree_totalassets. unfold octree_mtree.
    revert L4. clear. apply mtree_approx_fun_p_totalassets.
  }
  assert (L6: octree_approx_fun_p
                (tx_octree_trans 0 (tx_of_Block (bh, bd))
                                 (Some (ctree_of_Block (bh, bd))))
                (tx_statefun_trans 0 (tx_of_Block (bh, bd)) f)).
  { apply (octree_approx_trans tht' sigt' 0 (tx_of_Block (bh,bd)) (Some (ctree_of_Block (bh,bd))) f 0 (rewfn 0) Hf L3).
    unfold octree_approx_fun_p. unfold octree_mtree.
    exact HTf.
  }
  assert (L7: octree_approx_fun_p (Some T) (tx_statefun_trans 0 (tx_of_Block (bh, bd)) f)).
  { unfold octree_approx_fun_p. rewrite <- HT2.
    exact L6.
  }
  assert (L8: octree_totalassets (tx_octree_trans 0 (tx_of_Block (bh, bd)) (Some (ctree_of_Block (bh, bd)))) bl).
  { rewrite HT2.
    unfold octree_totalassets. unfold octree_mtree.
    apply (mtree_approx_fun_p_totalassets _ _ _ L7).
    revert H5b.
    unfold octree_totalassets. unfold octree_mtree.
    apply mtree_approx_fun_p_totalassets.
    revert L7. unfold octree_approx_fun_p.
    apply mtree_hashroot_mtree_approx_fun_p.
    unfold octree_mtree.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite ctree_hashroot_ctree_H.
    assert (E1: hashopair2 (ottree_hashroot tht2) (hashopair2 (ostree_hashroot sigt2) k2) = hashopair2 (ottree_hashroot (tx_update_ottree (tx_of_Block (bh, bd)) tht')) (hashopair2 (ostree_hashroot (tx_update_ostree (tx_of_Block (bh, bd)) sigt')) (ctree_hashroot T))).
    { transitivity (newledgerroot bh).
      - exact H5a.
      - exact HT1.
    }
    apply hashopair2inj in E1. destruct E1 as [_ E1].
    apply hashopair2inj in E1. destruct E1 as [_ E1].
    rewrite E1. reflexivity.
  }
  generalize (octree_tx_asset_value_sum tht' sigt' 0 (Some (ctree_of_Block (bh,bd))) (tx_of_Block (bh,bd)) 0 (rewfn 0) al bl L1 L2 L3 L5 L8).
  rewrite H3.
  assert (L9: asset_value_sum bl + 0 = asset_value_sum bl).
  { clear. omega. }
  rewrite L9.
  intros H. rewrite <- H. clear. omega.
- intros tht2 sigt2 k2 bl [H4 [tht' [sigt' H5]]] H6a H6b.
  generalize H5.
  intros [[H5aa [H5ab [H5ac [H5ad [H5ae [H5af [H5ag H5ah]]]]]]] [H5b [H5c [H5d [H5e [H5f [H5g [H5h [H5i [H5j [H5k [T [HT1 HT2]]]]]]]]]]]]].
  assert (Lplr: ledgerroot_valid plr).
  { revert H4. apply endledgerroot_plr_valid.
    exists tht. exists sigt. exists k.
    split.
    - symmetry. exact H0.
    - exact H1.
  }
  generalize Lplr. intros [tht3 [sigt3 [k3 [Hplr [f [Hf Hplrf]]]]]].
  assert (LIH: asset_value_sum (totalassets_ f) <= units_as_of_block initdistr rewfn (S n)).
  { apply (IH tht3 sigt3 k3).
    - exact H4.
    - symmetry. exact Hplr.
    - unfold octree_totalassets. unfold octree_mtree.
      apply (mtree_approx_fun_p_totalassets _ _ _ Hplrf).
      reflexivity.
  }
  change (asset_value_sum bl <= units_as_of_block initdistr rewfn (S n) + rewfn (S n)).
  transitivity (asset_value_sum (totalassets_ f) + rewfn (S n)).
  + assert (L0: hashopair2 (ottree_hashroot tht') (hashopair2 (ostree_hashroot sigt') (ctree_hashroot (ctree_of_Block(bh,bd)))) = plr).
    { 
      transitivity (hashopair2 (ottree_hashroot tht') (hashopair2 (ostree_hashroot sigt') (ctree_hashroot (prevledger bh)))).
      - f_equal. f_equal. unfold ctree_of_Block. symmetry.
        apply subqc_hashroot_eq. apply ctree_cgraft_subqc. exact H5i.
      - exact H5ad.
    }
    assert (L1: octree_valid (Some (ctree_of_Block (bh, bd)))).
    { unfold octree_valid. revert Lplr.
      intros [tht4 [sigt4 [k4 [H7 H8]]]].
      revert H8.
      unfold ctree_valid.
      apply mtree_hashroot_eq_valid.
      rewrite mtree_hashroot_ctree_hashroot.
      rewrite mtree_hashroot_ctree_hashroot.
      rewrite ctree_hashroot_ctree_H.
      f_equal.
      rewrite H7 in L0.
      apply hashopair2inj in L0. destruct L0 as [_ L0].
      apply hashopair2inj in L0. destruct L0 as [_ L0].
      exact L0.
    }
    assert (L2: tx_valid (tx_of_Block (bh, bd))).
    { revert H5. apply tx_of_Block_valid. }
    assert (L3: octree_supports_tx tht' sigt' (S n) (tx_of_Block (bh, bd)) (Some (ctree_of_Block (bh, bd))) 0 (rewfn (S n))).
    { unfold octree_supports_tx. revert L1 H5. unfold octree_valid. apply tx_of_Block_supported. }
    assert (LTf: octree_approx_fun_p (Some (ctree_of_Block (bh,bd))) f).
    { revert H5i. apply (endledgerroot_plr_valid_lem1 _ _ k3 ti bh bd f Hplrf).
      rewrite <- H5ad in Hplr.
      apply hashopair2inj in Hplr. destruct Hplr as [_ Hplr].
      apply hashopair2inj in Hplr. destruct Hplr as [_ Hplr].
      exact Hplr.
    }
    assert (L4: mtree_approx_fun_p (ctree_mtree (ctree_of_Block (bh,bd))) f).
    { revert Hplrf. apply mtree_hashroot_mtree_approx_fun_p.
      rewrite mtree_hashroot_ctree_hashroot.
      rewrite mtree_hashroot_ctree_hashroot.
      f_equal.
      rewrite Hplr in L0.
      apply hashopair2inj in L0. destruct L0 as [_ L0].
      apply hashopair2inj in L0. destruct L0 as [_ L0].
      rewrite <- L0.
      rewrite ctree_hashroot_ctree_H.
      reflexivity.
    }
    assert (L5: octree_totalassets (Some (ctree_of_Block (bh, bd))) (totalassets_ f)).
    { unfold octree_totalassets. unfold octree_mtree.
      apply (mtree_approx_fun_p_totalassets _ _ _ L4).
      reflexivity.
    }
    assert (L6: octree_approx_fun_p
                  (tx_octree_trans (S n) (tx_of_Block (bh, bd))
                                   (Some (ctree_of_Block (bh, bd))))
                  (tx_statefun_trans (S n) (tx_of_Block (bh, bd)) f)).
    { apply (octree_approx_trans tht' sigt' (S n) (tx_of_Block (bh,bd)) (Some (ctree_of_Block (bh,bd))) f 0 (rewfn (S n)) Hf L3).
      unfold octree_approx_fun_p. unfold octree_mtree.
      exact L4.
    }
    assert (L7: octree_approx_fun_p (Some T) (tx_statefun_trans (S n) (tx_of_Block (bh, bd)) f)).
    { unfold octree_approx_fun_p. rewrite <- HT2.
      exact L6.
    }
    assert (L8: octree_totalassets (tx_octree_trans (S n) (tx_of_Block (bh, bd)) (Some (ctree_of_Block (bh, bd)))) bl).
    { rewrite HT2.
      unfold octree_totalassets. unfold octree_mtree.
      apply (mtree_approx_fun_p_totalassets _ _ _ L7).
      revert H6b.
      unfold octree_totalassets. unfold octree_mtree.
      apply mtree_approx_fun_p_totalassets.
      revert L7. unfold octree_approx_fun_p.
      apply mtree_hashroot_mtree_approx_fun_p.
      unfold octree_mtree.
      rewrite mtree_hashroot_ctree_hashroot.
      rewrite mtree_hashroot_ctree_hashroot.
      rewrite ctree_hashroot_ctree_H.
      assert (E1: hashopair2 (ottree_hashroot tht2) (hashopair2 (ostree_hashroot sigt2) k2) = hashopair2 (ottree_hashroot (tx_update_ottree (tx_of_Block (bh, bd)) tht')) (hashopair2 (ostree_hashroot (tx_update_ostree (tx_of_Block (bh, bd)) sigt')) (ctree_hashroot T))).
      { transitivity (newledgerroot bh).
        - exact H6a.
        - exact HT1.
      }
      apply hashopair2inj in E1. destruct E1 as [_ E1].
      apply hashopair2inj in E1. destruct E1 as [_ E1].
      rewrite E1. reflexivity.
    }
    generalize (octree_tx_asset_value_sum tht' sigt' (S n) (Some (ctree_of_Block (bh,bd))) (tx_of_Block (bh,bd)) 0 (rewfn (S n)) (totalassets_ f) bl L1 L2 L3 L5 L8).
    assert (L9: asset_value_sum bl + 0 = asset_value_sum bl).
    { clear. omega. }
    rewrite L9. 
    intros H. rewrite <- H. clear. omega.
  + revert LIH. clear. intros H. omega.
Qed.
