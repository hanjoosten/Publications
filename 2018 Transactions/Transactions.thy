(*  assumes disjInsDel: "ins\<inter>del=\<emptyset>"

  File:    Transactions.thy
  Author:  Stef Joosten <stef.joosten@ou.nl>

  Proofs for Semantics of Transactions
*)

theory Transactions imports Main
begin

lemma Merge:
  assumes c1: "ins'-del'=ins'"
      and c2: "ins-del=ins"
      and c3: "(del\<union>del')-(ins\<union>ins')=del\<union>del'"
    shows "(((x-del)\<union>ins)-del')\<union>ins' = (x-(del\<union>del'))\<union>(ins\<union>ins')"
  by (metis (no_types, lifting) Diff_Diff_Int Diff_Int2 Diff_Un Diff_cancel Diff_empty Int_Diff Un_Diff abel_semigroup.left_commute c1 c3 inf_sup_absorb sup.abel_semigroup_axioms sup_bot.right_neutral sup_commute)

lemma Merge0:
  assumes c1: "ins'-del'=ins'"
      and c2: "(ins\<union>ins')-del' = ins\<union>ins'"
    shows "(((x-del)\<union>ins)-del')\<union>ins' = (x-(del\<union>del'))\<union>(ins\<union>ins')"
  using Diff_Diff_Int Diff_Un Diff_cancel Diff_empty Int_Diff c2 sup_commute by auto

end