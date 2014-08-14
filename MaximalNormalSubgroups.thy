(*  Title:      A locale for and a characterization of maximal normal subgroups
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
    Maintainer: Jakob von Raumer <jakob.raumer@student.kit.edu>
*)

theory MaximalNormalSubgroups
imports
  "SubgroupsAndNormalSubgroups"
  "SimpleGroups"
begin

section {* Facts about maximal normal subgroups *}

text {* A maximal normal subgroup of $G$ is a normal subgroup which is not contained in other any proper
  normal subgroup of $G$. *}

locale max_normal_subgroup = normal +
  assumes "H \<noteq> carrier G"
  assumes "\<And>J. J \<lhd> G \<Longrightarrow> J \<noteq> H \<Longrightarrow> J \<noteq> carrier G \<Longrightarrow> \<not> (H \<subseteq> J)"

text {* Another characterization of maximal normal subgroups: The factor group is simple. *}

theorem (in normal)
  shows "max_normal_subgroup H G = simple_group (G Mod H)"
proof
  assume "max_normal_subgroup H G"
  show "simple_group (G Mod H)" unfolding simple_group_def simple_group_axioms_def
  proof
    show "group (G Mod H)" by (rule factorgroup_is_group)
  next
    
  qed
qed
