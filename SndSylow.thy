(*  Title:      SndSylow.thy
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
*)

theory SndSylow
imports
  "~~/src/HOL/Algebra/Group"
  "~~/src/HOL/Algebra/Sylow"
  "~~/src/HOL/Algebra/Coset"
  "SubgroupConjugation"
  "GroupAction"
begin

lemma (in group) set_mult_inclusion:
  assumes H:"subgroup H G"
  assumes Q:"P \<subseteq> carrier G"
  assumes PQ:"H <#> P \<subseteq> H"
  shows "P \<subseteq> H"
proof
  fix x
  from H have "\<one> \<in> H" by (rule subgroup.one_closed)
  moreover assume x:"x \<in> P"
  ultimately have "\<one> \<otimes> x \<in> H <#> P" unfolding set_mult_def by auto
  with PQ have "\<one> \<otimes> x \<in> H" by auto
  with H Q x show  "x \<in> H" by (metis in_mono l_one)
qed

lemma card_eq_subset_imp_eq:
  assumes "A \<subseteq> B"
  assumes "finite B"
  assumes "card A = card B"
  shows "A = B"
using assms sledgehammer
by (metis card_seteq order_refl)

(*Second Sylow Theorems*)
locale snd_sylow = sylow +
  assumes pNotDvdm:"\<not> (p dvd m)"

lemma (in snd_sylow) ex_conj_sylow_group:
  assumes H:"H \<in> subgroups_of_size (p ^ b)"
  assumes Psize:"P \<in> subgroups_of_size (p ^ a)"
  obtains g where "g \<in> carrier G" "H \<subseteq> g <# (P #> inv g)"
proof -
  from H have HG:"H \<subseteq> carrier G" unfolding subgroups_of_size_def by (simp add:subgroup_imp_subset)
  from Psize have PG:"subgroup P G" and cardP:"card P = p ^ a" unfolding subgroups_of_size_def by auto
  def H' \<equiv> "G\<lparr>carrier := H\<rparr>"
  with H have orderH':"order H' =  p ^ b" unfolding subgroups_of_size_def order_def by simp
  def \<phi> \<equiv> "\<lambda>g \<in> carrier G. \<lambda>U. U #> inv g"
  with PG have "group_action G \<phi> (rcosets P)" by (metis is_group subgroup.inv_mult_on_rcosets_action)
  with H have H'action:"group_action H' \<phi> (rcosets P)" unfolding H'_def subgroups_of_size_def by (metis (mono_tags) group_action.subgroup_action mem_Collect_eq)
  from finite_G PG have "finite (rcosets P)" unfolding RCOSETS_def r_coset_def by (metis (lifting) finite.emptyI finite_UN_I finite_insert)
  with orderH' H'action sylow_axioms cardP have "card (group_action.fixed_points H' \<phi> (rcosets P)) mod p = card (rcosets P) mod p" unfolding sylow_def sylow_axioms_def by (metis group_action.fixed_point_congruence)
  moreover from finite_G PG order_G cardP  have "card (rcosets P) * p ^ a  = p ^ a * m" by (metis lagrange)
  with prime_p have "card (rcosets P) = m" by (metis less_nat_zero_code mult_cancel2 mult_is_0 nat_mult_commute order_G zero_less_o_G)
  hence "card (rcosets P) mod p = m mod p" by simp
  moreover from pNotDvdm prime_p have "... \<noteq> 0" by (metis dvd_eq_mod_eq_0)
  ultimately have "card (group_action.fixed_points H' \<phi> (rcosets P))  \<noteq> 0" by (metis mod_0)
  then obtain N where N:"N \<in> (group_action.fixed_points H' \<phi> (rcosets P))" by fastforce
  with H'action obtain g where g:"g \<in> carrier G" "N = P #> g" unfolding RCOSETS_def by (auto simp:group_action.fixed_points_def)
  hence invg:"inv g \<in> carrier G" by (metis inv_closed)
  hence invinvg:"inv (inv g) \<in> carrier G" by (metis inv_closed)
  from H'action N have "group_action.stabilizer H' \<phi> N = carrier H'" by (auto simp:group_action.fixed_points_def)
  with H'action have "\<forall>h\<in>H. \<phi> h N = N" unfolding H'_def by (auto simp:group_action.stabilizer_def)
  with HG have a1:"\<forall>h\<in>H. N #> inv h \<subseteq> N" unfolding \<phi>_def by fastforce
  have "N <#> H \<subseteq> N" unfolding set_mult_def r_coset_def
  proof(auto)
    fix n h
    assume n:"n \<in> N" and h:"h \<in> H"
    with H have "inv h \<in> H" by (metis (mono_tags) mem_Collect_eq subgroup.m_inv_closed subgroups_of_size_def)
    with n HG PG a1 have "n \<otimes> inv (inv h) \<in> N" unfolding r_coset_def by auto
    with HG h show  "n \<otimes> h \<in> N" by (metis in_mono inv_inv)
  qed
  with g have "((P #> g) <#> H) #> inv g \<subseteq> (P #> g) #> inv g" unfolding r_coset_def by auto
  with PG g invg have "((P #> g) <#> H) #> inv g \<subseteq> P" by (metis coset_mult_inv2 rcos_m_assoc subgroup_imp_subset)
  with g HG PG invg have "P <#> (g <# H #> inv g) \<subseteq> P" by (metis lr_coset_assoc r_coset_subset_G rcos_assoc_lcos setmult_rcos_assoc subgroup_imp_subset)
  with PG HG g invg have "g <# H #> inv g \<subseteq> P" by (metis l_coset_subset_G r_coset_subset_G set_mult_inclusion)
  with g have "(g <# H #> inv g) #> inv (inv g) \<subseteq> P #> inv (inv g)" unfolding r_coset_def by auto
  with HG g invg invinvg have "g <# H \<subseteq> P #> inv (inv g)" by (metis coset_mult_inv2 l_coset_subset_G rcos_m_assoc)
  with g have "(inv g) <# (g <# H) \<subseteq> inv g <# (P #> inv (inv g))" unfolding l_coset_def by auto
  with HG g invg invinvg have "H \<subseteq> inv g <# (P #> inv (inv g))" by (metis inv_inv lcos_m_assoc lcos_mult_one r_inv)
  with invg show thesis by (auto dest:that)
qed

section{*Every $p$-Group is Contained in a $p$-Sylow-Group*}

theorem (in snd_sylow) sylow_contained_in_sylow_group:
  assumes H:"H \<in> subgroups_of_size (p ^ b)"
  obtains S where "H \<subseteq> S" and "S \<in> subgroups_of_size (p ^ a)"
proof -
  from H have HG:"H \<subseteq> carrier G" unfolding subgroups_of_size_def by (simp add:subgroup_imp_subset)
  obtain P where PG:"subgroup P G" and cardP:"card P = p ^ a" by (metis sylow_thm)
  hence Psize:"P \<in> subgroups_of_size (p ^ a)" unfolding subgroups_of_size_def by simp
  with H obtain g where g:"g \<in> carrier G" "H \<subseteq> g <# (P #> inv g)" by (metis ex_conj_sylow_group)
  moreover note Psize g
  moreover with finite_G have "conjugation_action (p ^ a) g P \<in> subgroups_of_size (p ^ a)" by (metis conjugation_is_size_invariant)
  ultimately show thesis unfolding conjugation_action_def by (auto dest:that)
qed

section{*$p$-Sylow-Groups are conjugates of each other*}

theorem (in snd_sylow) sylow_conjugate:
  assumes P:"P \<in> subgroups_of_size (p ^ a)"
  assumes Q:"Q \<in> subgroups_of_size (p ^ a)"
  obtains g where "g \<in> carrier G" "Q = g <# (P #> inv g)"
proof -
  from P have "card P = p ^ a" unfolding subgroups_of_size_def by simp
  from Q have Qcard:"card Q = p ^ a" unfolding subgroups_of_size_def by simp
  from Q P obtain g where g:"g \<in> carrier G" "Q \<subseteq> g <# (P #> inv g)" by (rule ex_conj_sylow_group)
  moreover with P finite_G have "conjugation_action (p ^ a) g P \<in> subgroups_of_size (p ^ a)" by (metis conjugation_is_size_invariant)
  moreover from g P have "conjugation_action (p ^ a) g P = g <# (P #> inv g)" unfolding conjugation_action_def by simp
  ultimately have conjSize:"g <# (P #> inv g) \<in> subgroups_of_size (p ^ a)" unfolding conjugation_action_def by simp
  with Qcard have  card:"card (g <# (P #> inv g)) = card Q"  unfolding subgroups_of_size_def by simp
  from conjSize finite_G have "finite (g <# (P #> inv g))" by (metis (mono_tags) finite_subset mem_Collect_eq subgroup_imp_subset subgroups_of_size_def)
  with g card have "Q = g <# (P #> inv g)" by (metis card_eq_subset_imp_eq)
  with g show thesis by (metis that)
qed






