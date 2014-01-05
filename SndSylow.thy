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
  "CentralizerNormalizer"
begin

sledgehammer_params [provers = e spass remote_vampire remote_z3]
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

lemma (in group) card_subgrp_dvd:
  assumes "subgroup H G"
  shows "card H dvd order G"
proof(cases "finite (carrier G)")
  case True
  with assms have "card (rcosets H) * card H = order G" by (metis lagrange)
  thus ?thesis by (metis dvd_triv_left nat_mult_commute)
next
  case False
  hence "order G = 0" unfolding order_def by (metis card_infinite)
  thus ?thesis by (metis dvd_0_right)
qed

lemma card_eq_subset_imp_eq:
  assumes "A \<subseteq> B"
  assumes "finite B"
  assumes "card A = card B"
  shows "A = B"
using assms by (metis card_seteq order_refl)

lemma singletonI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> x = y"
  assumes "y \<in> A"
  shows "A = {y}"
using assms by fastforce
 

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
  def \<phi> \<equiv> "\<lambda>g. \<lambda>U\<in>rcosets P. U #> inv g"
  with PG have "group_action G \<phi> (rcosets P)" unfolding \<phi>_def by (metis inv_mult_on_rcosets_action)
  with H interpret H'act: group_action H' \<phi> "(rcosets P)" unfolding H'_def subgroups_of_size_def by (metis (mono_tags) group_action.subgroup_action mem_Collect_eq)
  from finite_G PG have "finite (rcosets P)" unfolding RCOSETS_def r_coset_def by (metis (lifting) finite.emptyI finite_UN_I finite_insert)
  with orderH' sylow_axioms cardP have "card H'act.fixed_points mod p = card (rcosets P) mod p" unfolding sylow_def sylow_axioms_def sorry (*by (metis group_action.fixed_point_congruence)*)
  moreover from finite_G PG order_G cardP  have "card (rcosets P) * p ^ a  = p ^ a * m" by (metis lagrange)
  with prime_p have "card (rcosets P) = m" by (metis less_nat_zero_code mult_cancel2 mult_is_0 nat_mult_commute order_G zero_less_o_G)
  hence "card (rcosets P) mod p = m mod p" by simp
  moreover from pNotDvdm prime_p have "... \<noteq> 0" by (metis dvd_eq_mod_eq_0)
  ultimately have "card H'act.fixed_points  \<noteq> 0" by (metis mod_0)
  then obtain N where N:"N \<in> H'act.fixed_points" by fastforce
  then obtain g where g:"g \<in> carrier G" "N = P #> g" unfolding RCOSETS_def (*by (auto simp:group_action.fixed_points_def)
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
qed*)
sorry show ?thesis sorry qed

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

corollary (in snd_sylow) sylow_conj_orbit_rel:
  assumes P:"P \<in> subgroups_of_size (p ^ a)"
  assumes Q:"Q \<in> subgroups_of_size (p ^ a)"
  shows "(P,Q) \<in> group_action.same_orbit_rel G (conjugation_action (p ^ a)) (subgroups_of_size (p ^ a))"
unfolding group_action.same_orbit_rel_def 
proof -
  from Q P obtain g where g:"g \<in> carrier G" "P = g <# (Q #> inv g)" by (rule sylow_conjugate)
  with Q P have g':"conjugation_action (p ^ a) g Q = P" unfolding conjugation_action_def by simp
  from finite_G interpret conj: group_action G "(conjugation_action (p ^ a))" "(subgroups_of_size (p ^ a))" by (rule acts_on_subsets)
  have "conj.same_orbit_rel = {X \<in> (subgroups_of_size (p ^ a) \<times> subgroups_of_size (p ^ a)). \<exists>g \<in> carrier G. ((conjugation_action (p ^ a)) g) (snd X) = (fst X)}" by (rule conj.same_orbit_rel_def)
  with g g' P Q show ?thesis by auto
qed

section{*Counting Sylow-Groups*}

(*The number of sylow groups is the orbit size of one of them*)
theorem (in snd_sylow) num_eq_card_orbit:
  assumes P:"P \<in> subgroups_of_size (p ^ a)"
  shows "subgroups_of_size (p ^ a) = group_action.orbit G (conjugation_action (p ^ a)) (subgroups_of_size (p ^ a)) P"
proof(auto)
  from finite_G interpret conj: group_action G "(conjugation_action (p ^ a))" "(subgroups_of_size (p ^ a))" by (rule acts_on_subsets)
  have "group_action.orbit G (conjugation_action (p ^ a)) (subgroups_of_size (p ^ a)) P = group_action.same_orbit_rel G (conjugation_action (p ^ a)) (subgroups_of_size (p ^ a)) `` {P}" by (rule conj.orbit_def)
  fix Q
  {
    assume Q:"Q \<in> subgroups_of_size (p ^ a)"
    from P Q obtain g where g:"g \<in> carrier G" "Q = g <# (P #> inv g) " by (rule sylow_conjugate)
    with P conj.orbit_char show "Q \<in> group_action.orbit G (conjugation_action (p ^ a)) (subgroups_of_size (p ^ a)) P"
      unfolding conjugation_action_def by auto
  } {
    assume "Q \<in> group_action.orbit G (conjugation_action (p ^ a)) (subgroups_of_size (p ^ a)) P"
    with P conj.orbit_char obtain g where g:"g \<in> carrier G" "Q = conjugation_action (p ^ a) g P" by auto
    with finite_G P show "Q \<in> subgroups_of_size (p ^ a)"  by (metis conjugation_is_size_invariant)
  }
qed

theorem (in snd_sylow) pa_not_zero:
  shows "p ^ a \<noteq> 0"
by (metis less_numeral_extra(3) prime_p zero_less_prime_power)

theorem (in snd_sylow) num_sylow_normalizer:
  assumes Psize:"P \<in> subgroups_of_size (p ^ a)"
  shows "card (rcosets\<^bsub>G\<lparr>carrier := group_action.stabilizer G (conjugation_action (p ^ a)) P\<rparr>\<^esub> P) * p ^ a = card (group_action.stabilizer G (conjugation_action (p ^ a)) P)"
proof -
  from finite_G interpret conj: group_action G "(conjugation_action (p ^ a))" "(subgroups_of_size (p ^ a))" by (rule acts_on_subsets)
  from Psize have PG:"subgroup P G" and cardP:"card P = p ^ a" unfolding subgroups_of_size_def by auto
  with finite_G have "order G = card (conj.orbit P) * card (conj.stabilizer P)" by (metis Psize acts_on_subsets group_action.orbit_size)
  with order_G Psize have "p ^ a * m = card (subgroups_of_size (p ^ a)) * card (conj.stabilizer P)" by (metis num_eq_card_orbit)
  moreover from Psize interpret stabGroup: group "G\<lparr>carrier := conj.stabilizer P\<rparr>" by (metis conj.stabilizer_is_subgroup subgroup_imp_group)
  from finite_G Psize have PStab:"subgroup P (G\<lparr>carrier := conj.stabilizer P\<rparr>)" by (rule stabilizer_supergrp_P)
  from finite_G Psize have "finite (conj.stabilizer P)" by (metis card_infinite conj.stabilizer_is_subgroup less_nat_zero_code subgroup.finite_imp_card_positive)
  with finite_G PStab stabGroup.lagrange have "card (rcosets\<^bsub>G\<lparr>carrier := conj.stabilizer P\<rparr>\<^esub> P) * card P = order (G\<lparr>carrier := conj.stabilizer P\<rparr>)" by force
  with cardP show ?thesis unfolding order_def by auto 
qed

theorem (in snd_sylow) num_sylow_dvd_remainder:
  shows "card (subgroups_of_size (p ^ a)) dvd m"
proof -
  from finite_G interpret conj: group_action G "(conjugation_action (p ^ a))" "(subgroups_of_size (p ^ a))" by (rule acts_on_subsets)
  obtain P where PG:"subgroup P G" and cardP:"card P = p ^ a" by (metis sylow_thm)
  hence Psize:"P \<in> subgroups_of_size (p ^ a)" unfolding subgroups_of_size_def by simp
  with finite_G have "order G = card (conj.orbit P) * card (conj.stabilizer P)" by (metis Psize acts_on_subsets group_action.orbit_size)
  with order_G Psize have orderEq:"p ^ a * m = card (subgroups_of_size (p ^ a)) * card (conj.stabilizer P)" by (metis num_eq_card_orbit)
  def k \<equiv> "card (rcosets\<^bsub>G\<lparr>carrier := conj.stabilizer P\<rparr>\<^esub> P)"
  with Psize have "k * p ^ a = card (conj.stabilizer P)" by (metis num_sylow_normalizer)
  with orderEq have "p ^ a * m = card (subgroups_of_size (p ^ a)) * p ^ a * k" by (auto simp:nat_mult_assoc nat_mult_commute)
  hence "p ^ a * m = p ^ a * card (subgroups_of_size (p ^ a)) * k" by auto
  with pa_not_zero have "m = card (subgroups_of_size (p ^ a)) * k" by auto
  thus ?thesis unfolding dvd_def by simp
qed


theorem (in snd_sylow) p_sylow_mod_p:
  shows "card (subgroups_of_size (p ^ a)) mod p = 1"
proof -
  obtain P where PG:"subgroup P G" and cardP:"card P = p ^ a" by (metis sylow_thm)
  hence orderP:"order (G\<lparr>carrier := P\<rparr>) = p ^ a" unfolding order_def by auto
  from PG have PsubG:"P \<subseteq> carrier G" by (metis subgroup_imp_subset)
  from PG cardP have PSize:"P \<in> subgroups_of_size (p ^ a)" unfolding subgroups_of_size_def by auto
  from PG interpret groupP:group "(G\<lparr>carrier := P\<rparr>)" by (rule subgroup_imp_group)
  have "subgroup P (G\<lparr>carrier := P\<rparr>)" using groupP.subgroup_self by force
  with cardP have PSize2:"P \<in> groupP.subgroups_of_size (p ^ a)" using groupP.subgroups_of_size_def by auto
  from finite_G interpret conjG: group_action G "conjugation_action (p ^ a)" "subgroups_of_size (p ^ a)" by (rule acts_on_subsets)
  from PG interpret conjP: group_action "G\<lparr>carrier := P\<rparr>" "conjugation_action (p ^ a)" "subgroups_of_size (p ^ a)" by (rule conjG.subgroup_action)
  from finite_G have "finite (subgroups_of_size (p ^ a))" unfolding subgroups_of_size_def subgroup_def by auto
  with orderP prime_p have "card (subgroups_of_size (p ^ a)) mod p = card conjP.fixed_points mod p" by (rule conjP.fixed_point_congruence)
  also have "... = 1"
  proof -
    have "\<And>Q. Q \<in> conjP.fixed_points \<Longrightarrow> Q = P"
    proof -
      fix Q
      assume Qfixed:"Q \<in> conjP.fixed_points"
      hence Qsize:"Q \<in> subgroups_of_size (p ^ a)" unfolding conjP.fixed_points_def by simp
      hence cardQ:"card Q = p ^ a" unfolding subgroups_of_size_def by simp
      (*The normalizer of Q in G*)
      def N \<equiv> "conjG.stabilizer Q"
      with Qsize have NG:"subgroup N G" by (metis conjG.stabilizer_is_subgroup)
      then interpret groupN: group "G\<lparr>carrier := N\<rparr>" by (metis subgroup_imp_group)
      from finite_G NG have finite_groupN:"finite (carrier (G\<lparr>carrier := N\<rparr>))" sorry
      with Qsize N_def have QN:"subgroup Q (G\<lparr>carrier := N\<rparr>)" using stabilizer_supergrp_P by auto
      from Qfixed Qsize have "\<forall>g\<in>N. conjugation_action (p ^ a) g Q = Q" using conjP.fixed_point_char by auto
      
      with PsubG have  "P \<subseteq> N" unfolding N_def conjG.stabilizer_def by auto
      with PG N_def Qsize have PN:"subgroup P (G\<lparr>carrier := N\<rparr>)" by (metis conjG.stabilizer_is_subgroup is_group subgroup.subgroup_of_subset)
      with cardP have "p ^ a dvd order (G\<lparr>carrier := N\<rparr>)" using groupN.card_subgrp_dvd by force
      hence "p ^ a dvd card N" unfolding order_def by simp
      then obtain k where cardN:"card N = p ^ a * k" unfolding dvd_def by auto
      moreover from NG order_G have "card N dvd (p ^ a * m)" using card_subgrp_dvd by auto
      ultimately obtain l where "p ^ a * k * l = p ^ a * m" unfolding dvd_def by auto
      hence "k * l = m" using mult_cancel2 nat_mult_assoc nat_mult_commute pa_not_zero by fastforce
      (*Instantiate the SndSylow Locale a second time for the normalizer of Q*)
      with prime_p have ndvd:"\<not> (p dvd k)" by (metis dvd_mult2 pNotDvdm)
      from cardN have orderN:"order (G\<lparr>carrier := N\<rparr>) = p ^ a * k" unfolding order_def by simp
      
      def NcalM \<equiv> "{s. s \<subseteq> carrier (G\<lparr>carrier := N\<rparr>) \<and> card s = p ^ a}"
      def NRelM \<equiv> "{(N1, N2). N1 \<in> NcalM \<and> N2 \<in> NcalM \<and> (\<exists>g\<in>carrier (G\<lparr>carrier := N\<rparr>). N1 = N2 #>\<^bsub>G\<lparr>carrier := N\<rparr>\<^esub> g)}"
      interpret Nsylow: snd_sylow "G\<lparr>carrier := N\<rparr>" p a k NcalM NRelM
        unfolding snd_sylow_def snd_sylow_axioms_def sylow_def sylow_axioms_def
        using groupN.is_group prime_p orderN finite_groupN ndvd NcalM_def NRelM_def by fastforce+
      (*P and Q are conjugate in N*)
      from cardP PN have PsizeN:"P \<in> groupN.subgroups_of_size (p ^ a)" unfolding groupN.subgroups_of_size_def by auto
      from cardQ QN have QsizeN:"Q \<in> groupN.subgroups_of_size (p ^ a)" unfolding groupN.subgroups_of_size_def by auto
      from QsizeN PsizeN obtain g where "g \<in> carrier (G\<lparr>carrier := N\<rparr>)" "P = g <#\<^bsub>G\<lparr>carrier := N\<rparr>\<^esub> (Q #>\<^bsub>G\<lparr>carrier := N\<rparr>\<^esub> inv\<^bsub>G\<lparr>carrier := N\<rparr>\<^esub> g)" by (rule Nsylow.sylow_conjugate)
      hence "P = g <# (Q #> inv g)" unfolding r_coset_def l_coset_def sorry
      
      show "Q = P" sorry
    qed
    moreover from finite_G PSize have "P \<in> conjP.fixed_points" using local.P_fixed_point_of_P_conj by auto
    ultimately have "conjP.fixed_points = {P}" by fastforce
    hence one:"card conjP.fixed_points = 1" by (auto simp: card_Suc_eq)
    with prime_p have "card conjP.fixed_points < p" unfolding prime_def by auto
    with one have "card conjP.fixed_points mod p = card conjP.fixed_points" using mod_pos_pos_trivial by auto
    with one show ?thesis by simp
  qed
  finally show ?thesis.
qed


