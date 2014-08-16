(*  Title:      The Jordan Hölder Theorem
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
    Maintainer: Jakob von Raumer <jakob.raumer@student.kit.edu>
*)

theory JordanHoelder
imports
  "CompositionSeries"
  "MaximalNormalSubgroups"
begin

locale jordan_hoelder = group
  + series\<HH>: composition_series G \<HH>
  + series\<GG>: composition_series G \<GG>
  for \<HH> and \<GG>

(*context jordan_hoelder
begin*)

lemma (in group) setmult_lcos_assoc:
     "\<lbrakk>H \<subseteq> carrier G; K \<subseteq> carrier G; x \<in> carrier G\<rbrakk>
      \<Longrightarrow> x <# K <#> H = x <# (K <#> H)"
by (force simp add: l_coset_def set_mult_def m_assoc)

lemma (in group) normal_subgroup_setmult:
  assumes M:"M \<lhd> G" and N:"N \<lhd> G"
  shows "M <#> N \<lhd> G"
proof (rule normalI, auto del:equalityI)
  from assms interpret sndiso:second_isomorphism_grp M G N
    unfolding second_isomorphism_grp_def second_isomorphism_grp_axioms_def normal_def by auto
  show "subgroup (M <#> N) G" by (rule sndiso.normal_set_mult_subgroup)
next
  fix g
  assume g:"g \<in> carrier G"
  have "M <#> N #> g = M <#> (N #> g)" using g M N setmult_rcos_assoc by (metis normal_inv_iff subgroup_imp_subset)
  also have "\<dots> = M <#> (g <# N)" using N g by (metis normal.coset_eq)
  also have "\<dots> = (M #> g) <#> N" using M N g by (metis normal_imp_subgroup rcos_assoc_lcos subgroup_imp_subset)
  also have "\<dots> = (g <# M) <#> N" using M g by (metis normal.coset_eq)
  also have "\<dots> = g <# (M <#> N)" using g M N setmult_lcos_assoc by (metis normal_inv_iff subgroup_imp_subset)
  finally show " M <#> N #> g = g <# (M <#> N)".
qed

theorem jordan_hoelder_quotients_using_permutations:
  assumes "group G"
  assumes "finite (carrier G)"
  assumes "composition_series G \<GG>"
  assumes "composition_series G \<HH>"
  shows "length \<GG> = length \<HH>"
    and "multiset_of normal_series.quotient_list G \<GG> = multiset_of normal_series.quotient_list G \<HH>"
using assms
proof (induction "length \<GG>" arbitrary: \<GG> \<HH> G rule: full_nat_induct)
  print_cases
  case 1
  print_cases
  case 1
  from "1.hyps"
  show ?case sorry
next
  case 1
  print_cases
  case 2
  then interpret comp\<GG>: composition_series G \<GG> by simp
  from 2 interpret comp\<HH>: composition_series G \<HH> by simp
  from 2 interpret grpG: group G by simp
  show ?case
  proof (cases "length \<GG> \<le> 3")
  next
    find_theorems "length \<GG>"
    case True
    hence  "length \<GG> = 0 \<or> length \<GG> = 1 \<or> length \<GG> = 2 \<or> length \<GG> = 3" by arith
    with comp\<GG>.notempty have  "length \<GG> = 1 \<or> length \<GG> = 2 \<or> length \<GG> = 3" by simp
    thus ?thesis
    proof auto
      -- {* First trivial case: \<GG> is the trivial group. *}
      assume "length \<GG> = Suc 0"
      hence length:"length \<GG> = 1" by simp
      hence "length [] + 1 = length \<GG>" by auto
      moreover from length have char\<GG>:"\<GG> = [{\<one>\<^bsub>G\<^esub>}]" by (metis comp\<GG>.composition_series_length_one)
      hence "carrier G = {\<one>\<^bsub>G\<^esub>}" by (metis comp\<GG>.composition_series_triv_group)
      with length char\<GG> have "\<GG> = \<HH>" using comp\<HH>.composition_series_triv_group by simp
      thus ?thesis by simp
    next
      -- {* Second trivial case: \<GG> is simple. *}
      assume "length \<GG> = 2"
      hence \<GG>char:"\<GG> = [{\<one>\<^bsub>G\<^esub>}, carrier G]" by (metis comp\<GG>.length_two_unique)
      hence simple:"simple_group G" by (metis comp\<GG>.composition_series_simple_group)
      hence "\<HH> = [{\<one>\<^bsub>G\<^esub>}, carrier G]" using comp\<HH>.composition_series_simple_group by auto
      with \<GG>char have "\<GG> = \<HH>" by simp
      thus ?thesis by simp
    next
      -- {* Not as trivial: \<GG> has length 3. *}
      assume length:"length \<GG> = 3"
      -- {* First we show that \<HH> must have a length of at least 3. *}
      hence "\<not> simple_group G" using comp\<GG>.composition_series_simple_group by auto
      hence "\<HH> \<noteq> [{\<one>\<^bsub>G\<^esub>}, carrier G]" using comp\<HH>.composition_series_simple_group by auto
      hence "length \<HH> \<noteq> 2" using comp\<HH>.length_two_unique by auto
      moreover from length have "carrier G \<noteq> {\<one>\<^bsub>G\<^esub>}" using comp\<GG>.composition_series_length_one comp\<GG>.composition_series_triv_group by auto
      hence "length \<HH> \<noteq> 1" using comp\<HH>.composition_series_length_one comp\<HH>.composition_series_triv_group by auto
      moreover from comp\<HH>.notempty have "length \<HH> \<noteq> 0" by simp
      ultimately have length\<HH>big:"length \<HH> \<ge> 3" using comp\<HH>.notempty by arith
      def l \<equiv> "length \<HH> - 1"
      show ?thesis
      proof (cases "\<HH> ! (l - 1) = \<GG> ! 1")
        -- {* If \<HH> ! (l - 1) = \<GG> ! 1, everything is simple... *}
        case True
        from length have "simple_group (G\<lparr>carrier := \<GG> ! 1\<rparr>)" by (metis comp\<GG>.composition_series_snd_simple le_add2 one_plus_numeral semiring_norm(3))
        with True have "simple_group (G\<lparr>carrier := \<HH> ! (l - 1)\<rparr>)" by simp
        hence lchar:"l - 1 = 1" by (metis comp\<HH>.composition_snd_simple_iff comp\<HH>.notempty diff_less l_def length_greater_0_conv less_imp_diff_less zero_less_one)
        hence length\<HH>:"length \<HH> = 3" unfolding l_def by simp
        have eq0:"\<GG> ! 0 = \<HH> ! 0" using hd_conv_nth comp\<GG>.hd comp\<HH>.hd comp\<GG>.notempty comp\<HH>.notempty by metis
        moreover have eq1:"\<GG> ! 1 = \<HH> ! 1" using True lchar by simp
        moreover have eq2:"\<GG> ! 2 = \<HH> ! 2" using length last_conv_nth comp\<GG>.notempty comp\<GG>.last length\<HH> last_conv_nth comp\<HH>.notempty comp\<HH>.last by force
        -- {* TODO: do this more gracefully *}
        ultimately have "\<And>i. i < length \<GG> \<Longrightarrow> \<GG> ! i = \<HH> ! i"
        proof -
          fix i
          assume i:"i < length \<GG>"
          hence "i = 0 \<or> i = 1 \<or> i = 2" using length by arith
          with eq0 eq1 eq2 show "\<GG> ! i = \<HH> ! i" by auto
        qed
        hence "\<GG> = \<HH>" using length length\<HH> by (metis list_eq_iff_nth_eq)
        thus ?thesis by simp
      next
        case False
        -- {* If \<HH> ! (l - 1) \<noteq> \<GG> ! 1, we have to take a closer look at the quotients: *}
        -- {* (\<GG> ! 1) \<inter> (\<HH> ! (l - 1)) is a normal subgroup of (\<GG> ! 1) *}
        have "(\<GG> ! 1) \<inter> (\<HH> ! (l - 1)) \<lhd> (G\<lparr>carrier := (\<GG> ! 1)\<rparr>)"
          apply (rule second_isomorphism_grp.normal_subgrp_intersection_normal)
          unfolding second_isomorphism_grp_def second_isomorphism_grp_axioms_def l_def
          using comp\<HH>.normal_series_snd_to_last length comp\<GG>.normal_series_snd_to_last normal_imp_subgroup
          by (metis One_nat_def Suc_1 diff_Suc_1 diff_Suc_eq_diff_pred normal_imp_subgroup numeral_3_eq_3)
          find_theorems "simple_group (G\<lparr>carrier :=  \<GG> ! 1\<rparr>)"
        -- {* And since (\<GG> ! 1) is simple its either trivial or (\<GG> ! 1) itself. *}
        hence "(\<GG> ! 1) \<inter> (\<HH> ! (l - 1)) = {\<one>\<^bsub>G\<^esub>} \<or> (\<GG> ! 1) \<subseteq> (\<HH> ! (l - 1))"
          using comp\<GG>.composition_series_snd_simple unfolding simple_group_def simple_group_axioms_def length
          by auto
        moreover 
        have "max_normal_subgroup (\<GG> ! (length \<GG> - 2)) G" using length comp\<GG>.snd_to_last_max_normal
          by (metis "2"(2) one_less_numeral_iff semiring_norm(77))
        with length have G1max:"max_normal_subgroup (\<GG> ! 1) G" by auto
        have lminus1:"l - 1 = length \<HH> - 2" unfolding l_def using length\<HH>big by auto
        hence HnormG:"\<HH> ! (l - 1) \<lhd> G" unfolding l_def using comp\<HH>.normal_series_snd_to_last by auto
        have "\<HH> ! (l - 1) \<noteq> carrier G" unfolding l_def
          using "2"(2)unfolding l_def 
          by (metis One_nat_def lminus1 `length \<HH> \<noteq> 0` `length \<HH> \<noteq> 1` comp\<HH>.snd_to_last_max_normal l_def less_Suc0 max_normal_subgroup.proper nat_neq_iff)
        with HnormG G1max have "\<not> (\<GG> ! 1) \<subseteq> (\<HH> ! (l - 1))"
          unfolding max_normal_subgroup_def max_normal_subgroup_axioms_def
          using False by auto
        ultimately have intertriv:"(\<GG> ! 1) \<inter> (\<HH> ! (l - 1)) = {\<one>\<^bsub>G\<^esub>}" by simp
        find_theorems "?a \<subseteq> ?x <#>\<^bsub>?G\<^esub> ?y"
        have "\<GG> ! 1 \<subseteq> (\<GG> ! 1) <#>\<^bsub>G\<^esub> (\<HH> ! (l - 1))"
          using second_isomorphism_grp.H_contained_in_set_mult
          unfolding second_isomorphism_grp_def second_isomorphism_grp_axioms_def
          using G1max HnormG normal_imp_subgroup
          unfolding max_normal_subgroup_def by metis
        moreover have "\<GG> ! 1 \<noteq> (\<GG> ! 1) <#>\<^bsub>G\<^esub> \<HH> ! (l - 1)" 
        proof -
          have "\<HH> ! (l - 1) \<noteq> {\<one>\<^bsub>G\<^esub>}" using lminus1 length\<HH>big comp\<HH>.inner_elements_not_triv by fastforce
          then obtain h where h:"h \<in> \<HH> ! (l - 1)" and "h \<noteq> \<one>\<^bsub>G\<^esub>" using HnormG normal_imp_subgroup subgroup.one_closed by fastforce
          hence "h \<notin> \<GG> ! 1" using intertriv by auto
          moreover from h have "\<one>\<^bsub>G\<^esub> \<otimes>\<^bsub>G\<^esub> h \<in> (\<GG> ! 1) <#>\<^bsub>G\<^esub> \<HH> ! (l - 1)"
            unfolding set_mult_def using G1max unfolding max_normal_subgroup_def using normal_imp_subgroup
            using subgroup.one_closed by fastforce
          hence "h \<in> (\<GG> ! 1) <#>\<^bsub>G\<^esub> \<HH> ! (l - 1)" using comp\<GG>.l_one h HnormG normal_imp_subgroup subgroup_imp_subset by force
          ultimately show ?thesis by metis
        qed
        ultimately have "(\<GG> ! 1) <#>\<^bsub>G\<^esub> (\<HH> ! (l - 1)) = carrier G" using G1max HnormG comp\<GG>.normal_subgroup_setmult
          unfolding max_normal_subgroup_def max_normal_subgroup_axioms_def by metis
        -- {* Find suitable isomophisms to show  G\<lparr>carrier := (\<HH> ! (l - 1))\<rparr> \<cong> G Mod (\<GG> ! 1)*}
        then obtain \<phi> where "\<phi> \<in> G\<lparr>carrier := (\<HH> ! (l - 1))\<rparr> Mod {\<one>\<^bsub>G\<^esub>} \<cong> G\<lparr>carrier := carrier G\<rparr> Mod (\<GG> ! 1)"
          using G1max HnormG normal_imp_subgroup second_isomorphism_grp.normal_intersection_quotient_isom intertriv
          unfolding max_normal_subgroup_def second_isomorphism_grp_def second_isomorphism_grp_axioms_def
          by metis
        hence \<phi>:"\<phi> \<in> G\<lparr>carrier := (\<HH> ! (l - 1))\<rparr> Mod {\<one>\<^bsub>G\<^esub>} \<cong> G Mod (\<GG> ! 1)" by auto
        obtain \<psi> where "\<psi> \<in> G\<lparr>carrier := (\<HH> ! (l - 1))\<rparr> Mod {\<one>\<^bsub>G\<lparr>carrier := (\<HH> ! (l - 1))\<rparr>\<^esub>} \<cong> G\<lparr>carrier := (\<HH> ! (l - 1))\<rparr>"
          using HnormG normal_imp_subgroup comp\<GG>.subgroup_imp_group group.trivial_factor_iso
          by metis
        hence \<psi>:"\<psi> \<in> G\<lparr>carrier := (\<HH> ! (l - 1))\<rparr> Mod {\<one>\<^bsub>G\<^esub>} \<cong> G\<lparr>carrier := (\<HH> ! (l - 1))\<rparr>" by auto
        have "{\<one>\<^bsub>G\<^esub>} \<lhd> G\<lparr>carrier := (\<HH> ! (l - 1))\<rparr>"
          using HnormG normal_imp_subgroup comp\<GG>.subgroup_imp_group group.triv_normal_subgroup by force
        hence "group (G\<lparr>carrier := (\<HH> ! (l - 1))\<rparr> Mod {\<one>\<^bsub>G\<^esub>})" by (rule normal.factorgroup_is_group)
        with \<psi> have "inv_into (carrier (G\<lparr>carrier := (\<HH> ! (l - 1))\<rparr> Mod {\<one>\<^bsub>G\<^esub>})) \<psi> \<in> G\<lparr>carrier := (\<HH> ! (l - 1))\<rparr> \<cong> G\<lparr>carrier := (\<HH> ! (l - 1))\<rparr> Mod {\<one>\<^bsub>G\<^esub>}"
          using group.iso_sym by auto
        with \<phi> obtain \<phi>' where "\<phi>' \<in> G\<lparr>carrier := (\<HH> ! (l - 1))\<rparr> \<cong> G Mod (\<GG> ! 1)"
          using HnormG normal_imp_subgroup comp\<GG>.subgroup_imp_group group.iso_trans by metis
        
      qed
    qed
  qed
qed

theorem jordan_hoelder_quotients_using_permutations:
  assumes "group G"
  assumes "composition_series G \<GG>"
  assumes "composition_series G \<HH>"
  shows "length \<GG> = length \<HH>" and "((\<And>isoms \<pi>. length isoms + 1 = length \<GG> \<Longrightarrow>
        \<pi> \<in> Bij {0..<length \<GG> - 1} \<Longrightarrow>
        (\<And>i. i + 1 < length \<GG> \<Longrightarrow> isoms ! i \<in> normal_series.quotient_list G \<GG> ! i \<cong> normal_series.quotient_list G \<HH> ! \<pi> i) \<Longrightarrow>
        thesis) \<Longrightarrow> thesis)" using assms
proof (induction "length \<GG>" arbitrary: \<GG> \<HH> G rule: full_nat_induct)
  print_cases
  case 1
  print_cases
  case 1
  from "1.hyps"
  show ?case sorry
next
  case 1
  case 2
  then interpret comp\<GG>: composition_series G \<GG> by simp
  from 2 interpret comp\<HH>: composition_series G \<HH> by simp
  from 2 interpret grpG: group G by simp
  show thesis
  proof (cases "length \<GG> \<le> 2")
    case True
    hence "length \<GG> = 0 \<or> length \<GG> = 1 \<or> length \<GG> = 2" by arith
    with comp\<GG>.notempty have "length \<GG> = 1 \<or> length \<GG> = 2" by auto
    thus thesis
    proof (rule disjE)
      -- {* First trivial case: The series has length 1. *}
      
      assume length:"length \<GG> = 1"
      hence "length [] + 1 = length \<GG>" by auto
      moreover from length have "\<GG> = [{\<one>\<^bsub>G\<^esub>}]" by (metis comp\<GG>.composition_series_length_one)
      hence "carrier G = {\<one>\<^bsub>G\<^esub>}" by (metis comp\<GG>.composition_series_triv_group)
      hence "length \<HH> = 1" using comp\<HH>.composition_series_triv_group by simp
      with length have "length \<GG> = length \<HH>" by simp
      moreover from length have empty:"{0 ..< length \<GG> - 1} = {}" by auto
      then obtain \<pi> where "\<pi> \<in> (extensional {0 ..< length \<GG> - 1}::((nat \<Rightarrow> nat) set))" by (metis restrict_extensional)
      with empty have "\<pi> \<in> Bij {0 ..< length \<GG> - 1}" unfolding Bij_def bij_betw_def by simp
      ultimately show thesis using 2 by auto
    next
      -- {* Second trivial case: The series has length 2. *}
      assume length:"length \<GG> = 2"
      hence \<GG>char:"\<GG> = [{\<one>\<^bsub>G\<^esub>}, carrier G]" by (metis comp\<GG>.length_two_unique)
      hence simple:"simple_group G" by (metis comp\<GG>.composition_series_simple_group)
      hence "\<HH> = [{\<one>\<^bsub>G\<^esub>}, carrier G]" and length':"length \<HH> = 2" using comp\<HH>.composition_series_simple_group by auto
      with \<GG>char length have "comp\<GG>.quotient_list = [G Mod {\<one>\<^bsub>G\<^esub>}]" "comp\<HH>.quotient_list = [G Mod {\<one>\<^bsub>G\<^esub>}]"
        unfolding comp\<HH>.quotient_list_def comp\<GG>.quotient_list_def by auto
      hence eq_quotients:"comp\<GG>.quotient_list = comp\<HH>.quotient_list" by simp
      have "length [(\<lambda>x. x)] + 1 = length \<GG>" using length by simp
      moreover from length length' have "length \<GG> = length \<HH>" by simp
      moreover have "(\<lambda>x\<in>{0..<length \<GG> - 1}.x) \<in> Bij {0 ..< length \<GG> - 1}" using length unfolding Bij_def bij_betw_def by simp
      ultimately show thesis using 2 eq_quotients iso_refl length by fastforce
    qed 
  next
    -- {* Non-trivial case: The series is of length $\gt 2$. *}
    case False
    hence length:"length \<GG> \<ge> 3" by simp
    then obtain k where k:"length \<GG> = Suc k" by (metis Suc_eq_plus1 comp\<GG>.quotient_list_length)
    hence k2:"k \<ge> 2" using length by arith+
    with k have ksmall:"(k - 1) + 1 < length \<GG>" by auto
    def G' \<equiv> "\<GG> ! (k - 1)"
    hence "G' \<lhd> G\<lparr>carrier := \<GG> ! ((k - 1) + 1)\<rparr>" using ksmall comp\<GG>.normal by auto
    hence G'G:"G' \<lhd> G" unfolding G'_def using k2 k comp\<GG>.last last_conv_nth comp\<GG>.notempty by fastforce
    have "simple_group (G\<lparr>carrier := \<GG> ! ((k - 1) + 1)\<rparr> Mod G')" 
      unfolding G'_def using ksmall comp\<GG>.simplefact by auto
    hence simpGG':"simple_group (G Mod G')" unfolding G'_def using k2 k comp\<GG>.last last_conv_nth comp\<GG>.notempty by fastforce
    obtain l where l:"length \<HH> = l + 1" using comp\<HH>.notempty by (metis comp\<HH>.quotient_list_length)
    show thesis
    proof (cases "l \<ge> k")
      case False
      with l k have le:"Suc (length \<HH>) \<le> length \<GG>" by simp
      moreover hence "length \<HH> = length \<GG>" using "1.hyps" "1.prems" by blast
      ultimately have "False" by auto
      thus thesis.. (*This still seems fishy to me, maybe wrong hyp?*)
    next
      case True
      hence l2:"l \<ge> 2" using l k k2 by simp
      with l k have lsmall:"(l - 1) + 1 < length \<HH>" by auto
      def H' \<equiv> "\<HH> ! (l - 1)"
      hence "H' \<lhd> G\<lparr>carrier := \<HH> ! ((l - 1) + 1)\<rparr>" using lsmall comp\<HH>.normal by auto
      hence H'G:"H' \<lhd> G" unfolding H'_def using l l2 comp\<HH>.last last_conv_nth comp\<HH>.notempty by fastforce
      then interpret snd_isoG'H': second_isomorphism_grp G' G H'
        using G'G unfolding second_isomorphism_grp_def second_isomorphism_grp_axioms_def using normal_imp_subgroup
        by auto
      def N \<equiv> "G' \<inter> H'"
      with H'G G'G have NG:"N \<lhd> G" by (metis comp\<GG>.normal_subgroup_intersect)
      show thesis
      proof (cases "N = {\<one>\<^bsub>G\<^esub>}")
        case True
        have "G' \<noteq> H'"
        proof (rule notI)
          assume "G' = H'"
          with True have "G' = {\<one>\<^bsub>G\<^esub>}" "H' = {\<one>\<^bsub>G\<^esub>}" unfolding N_def by auto
          with length k k2 show "False" unfolding G'_def H'_def using comp\<GG>.inner_elements_not_triv by auto
        qed
        have "G' <#>\<^bsub>G\<^esub> H' \<lhd> G" by (metis G'G H'G comp\<GG>.normal_subgroup_setmult)
        hence "carrier (G\<lparr>carrier := (G' <#>\<^bsub>G\<^esub> H')\<rparr> Mod G') \<lhd> G Mod G'"
          using comp\<GG>.normality_factorization snd_isoG'H'.H_contained_in_set_mult G'G
          unfolding FactGroup_def by auto
        hence "carrier (G\<lparr>carrier := (G' <#>\<^bsub>G\<^esub> H')\<rparr> Mod G') = {\<one>\<^bsub>G Mod G'\<^esub>}
          \<or> carrier (G\<lparr>carrier := (G' <#>\<^bsub>G\<^esub> H')\<rparr> Mod G') = carrier (G Mod G')"
          using simpGG' unfolding simple_group_def simple_group_axioms_def by auto
        moreover have "carrier (G\<lparr>carrier := (G' <#>\<^bsub>G\<^esub> H')\<rparr> Mod G') \<noteq> {\<one>\<^bsub>G Mod G'\<^esub>}" sorry
        ultimately have "carrier (G\<lparr>carrier := (G' <#>\<^bsub>G\<^esub> H')\<rparr> Mod G') = carrier (G Mod G')" by simp
        then obtain bla where  iso:"bla \<in> (G Mod H') \<cong> G\<lparr>carrier := G'\<rparr>" sorry
        have "simple_group (G Mod H')" sorry
        hence "simple_group (G\<lparr>carrier := G'\<rparr>)" by (metis iso comp\<GG>.is_group simple_group.iso_simple snd_isoG'H'.subgroup_is_group)
        hence "k = 2" sorry
        show thesis sorry
      next
        case False
        show thesis sorry
      qed
    qed
  qed
qed
oops

text {* As a corollary, we see that the composition series of a fixed group
all have the same length. *}

corollary jordan_hoelder_size:
  shows "length \<GG> = length \<HH>"
proof -
  obtain isoms where length:"length isoms + 1 = length \<GG>"
    and isoms:"multiset_of (map (\<lambda>(x,y). x y) (zip isoms series\<GG>.quotient_list)) = multiset_of series\<HH>.quotient_list" by (rule jordan_hoelder_quotients)
  have "length \<GG> = min (length series\<GG>.quotient_list + 1) (length isoms + 1)" using length by (auto simp: series\<GG>.quotient_list_length[symmetric])
  also have "... = min (length series\<GG>.quotient_list) (length isoms) + 1" by auto
  also have "... = length (map (\<lambda>(x,y). x y) (zip isoms series\<GG>.quotient_list)) + 1" using length_zip by auto
  also have "... = length series\<HH>.quotient_list + 1" using isoms by (metis size_multiset_of)
  also have "length series\<HH>.quotient_list + 1 = length \<HH>" by (rule series\<HH>.quotient_list_length)
  finally show ?thesis .
qed

end

end
