(*  Title:      The Jordan-Hölder Theorem
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
    Maintainer: Jakob von Raumer <jakob.raumer@student.kit.edu>
*)

theory JordanHoelder
imports
  "CompositionSeries"
  "MaximalNormalSubgroups"
  "Multiset"
  "GroupIsoClasses"
begin

locale jordan_hoelder = group
  + comp\<HH>: composition_series G \<HH>
  + comp\<GG>: composition_series G \<GG> for \<HH> and \<GG>
  + assumes finite:"finite (carrier G)"

lemma (in group) setmult_lcos_assoc:
     "\<lbrakk>H \<subseteq> carrier G; K \<subseteq> carrier G; x \<in> carrier G\<rbrakk>
      \<Longrightarrow> (x <#\<^bsub>G\<^esub> K) <#> H = x <# (K <#> H)"
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
  also have "\<dots> = M <#> (g <#\<^bsub>G\<^esub> N)" using N g by (metis normal.coset_eq)
  also have "\<dots> = (M #> g) <#> N" using M N g by (metis normal_imp_subgroup rcos_assoc_lcos subgroup_imp_subset)
  also have "\<dots> = (g <#\<^bsub>G\<^esub> M) <#> N" using M g by (metis normal.coset_eq)
  also have "\<dots> = g <# (M <#> N)" using g M N setmult_lcos_assoc by (metis normal_inv_iff subgroup_imp_subset)
  finally show " M <#> N #> g = g <# (M <#> N)".
qed

lemma (in composition_series) quotients_butlast:
  assumes "length \<GG> > 1"
  shows "butlast quotients = normal_series.quotients (G\<lparr>carrier := \<GG> ! (length \<GG> - 1 - 1)\<rparr>) (take (length \<GG> - 1) \<GG>)"
proof (rule nth_equalityI )
  def n \<equiv> "length \<GG> - 1"
  hence "n = length (take n \<GG>)" "n > 0" "n < length \<GG>" using assms notempty by auto
  interpret comp\<GG>butlast: composition_series "(G\<lparr>carrier := \<GG> ! (n - 1)\<rparr>)" "take n \<GG>" 
    using composition_series_prefix_closed `n > 0` `n < length \<GG>` by auto
  have "length (butlast quotients) = length quotients - 1" by (metis length_butlast)
  also have "\<dots> = length \<GG> - 1 - 1" by (metis add_diff_cancel_right' quotients_length)
  also have "\<dots> = length (take n \<GG>) - 1" by (metis `n = length (take n \<GG>)` n_def)
  also have "\<dots> = length comp\<GG>butlast.quotients" by (metis comp\<GG>butlast.quotients_length diff_add_inverse2)
  finally show "length (butlast quotients) = length comp\<GG>butlast.quotients" .
  have "\<forall>i<length (butlast quotients). butlast quotients ! i = comp\<GG>butlast.quotients ! i"
  proof auto
    fix i
    assume i:"i < length quotients - Suc 0"
    hence i':"i < length \<GG> - 1" "i < n" "i + 1 < n" unfolding n_def using quotients_length by auto
    from i have "butlast quotients ! i = quotients ! i" by (metis One_nat_def length_butlast nth_butlast)
    also have "\<dots> = G\<lparr>carrier := \<GG> ! (i + 1)\<rparr> Mod \<GG> ! i" unfolding quotients_def using i'(1) by auto
    also have "\<dots> = G\<lparr>carrier := (take n \<GG>) ! (i + 1)\<rparr> Mod (take n \<GG>) ! i" using i'(2,3) nth_take by metis
    also have "\<dots> = comp\<GG>butlast.quotients ! i" unfolding comp\<GG>butlast.quotients_def using i' by fastforce
    finally show "butlast (normal_series.quotients G \<GG>) ! i = normal_series.quotients (G\<lparr>carrier := \<GG> ! (n - Suc 0)\<rparr>) (take n \<GG>) ! i" by auto
  qed
  thus "\<forall>i<length (butlast quotients). butlast quotients ! i
    = normal_series.quotients (G\<lparr>carrier := \<GG> ! (length \<GG> - 1 - 1)\<rparr>)  (take (length \<GG> - 1) \<GG>) ! i"
    unfolding n_def by auto
qed

text {* The main part of the Jordan Hölder theorem is its statement about the uniqueness of 
  a composition series. Here, uniqueness up to reordering and isomorphism is modelled by stating
  that the multisets of isomorphism classes of all quotients are equal. *}

theorem jordan_hoelder_multisets:
  assumes "group G"
  assumes "finite (carrier G)"
  assumes "composition_series G \<GG>"
  assumes "composition_series G \<HH>"
  shows "multiset_of (map group.iso_class (normal_series.quotients G \<GG>))
    = multiset_of (map group.iso_class (normal_series.quotients G \<HH>))"
using assms
proof (induction "length \<GG>" arbitrary: \<GG> \<HH> G rule: full_nat_induct)
  print_cases
  case (1 \<GG> \<HH> G)
  then interpret comp\<GG>: composition_series G \<GG> by simp
  from 1 interpret comp\<HH>: composition_series G \<HH> by simp
  from 1 interpret grpG: group G by simp
  show ?case
  proof (cases "length \<GG> \<le> 2")
  next
    case True
    hence  "length \<GG> = 0 \<or> length \<GG> = 1 \<or> length \<GG> = 2" by arith
    with comp\<GG>.notempty have  "length \<GG> = 1 \<or> length \<GG> = 2" by simp
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
    qed
  next
    case False
    -- {* Non-trivial case: \<GG> has length at least 3. *}
    hence length:"length \<GG> \<ge> 3" by simp
    -- {* First we show that \<HH> must have a length of at least 3. *}
    hence "\<not> simple_group G" using comp\<GG>.composition_series_simple_group by auto
    hence "\<HH> \<noteq> [{\<one>\<^bsub>G\<^esub>}, carrier G]" using comp\<HH>.composition_series_simple_group by auto
    hence "length \<HH> \<noteq> 2" using comp\<HH>.length_two_unique by auto
    moreover from length have "carrier G \<noteq> {\<one>\<^bsub>G\<^esub>}" using comp\<GG>.composition_series_length_one comp\<GG>.composition_series_triv_group by auto
    hence "length \<HH> \<noteq> 1" using comp\<HH>.composition_series_length_one comp\<HH>.composition_series_triv_group by auto
    moreover from comp\<HH>.notempty have "length \<HH> \<noteq> 0" by simp
    ultimately have length\<HH>big:"length \<HH> \<ge> 3" using comp\<HH>.notempty by arith
    def m \<equiv> "length \<HH> - 1"
    def n \<equiv> "length \<GG> - 1"
    from length\<HH>big have m':"m > 0" "m < length \<HH>" "(m - 1) + 1 < length \<HH>" "m - 1 = length \<HH> - 2" "m - 1 + 1 = length \<HH> - 1" "m - 1 < length \<HH>"
      unfolding m_def by auto
    from length have n':"n > 0" "n < length \<GG>" "(n - 1) + 1 < length \<GG>" "n - 1 < length \<GG>" "Suc n \<le> length \<GG>"
     "n - 1 = length \<GG> - 2" "n - 1 + 1 = length \<GG> - 1"  unfolding n_def by auto
    def \<GG>Pn \<equiv> "G\<lparr>carrier := \<GG> ! (n - 1)\<rparr>"
    def \<HH>Pm \<equiv> "G\<lparr>carrier := \<HH> ! (m - 1)\<rparr>"
    then interpret grp\<GG>Pn: group \<GG>Pn unfolding \<GG>Pn_def using n' by (metis comp\<GG>.normal_series_subgroups comp\<GG>.subgroup_imp_group)
    interpret grp\<HH>Pm: group \<HH>Pm unfolding \<HH>Pm_def using m' comp\<HH>.normal_series_subgroups 1(2) group.subgroup_imp_group by force
    have finGbl:"finite (carrier \<GG>Pn)" using `n - 1 < length \<GG>` 1(3) unfolding \<GG>Pn_def using comp\<GG>.normal_series_subgroups comp\<GG>.subgroup_finite by auto
    have finHbl:"finite (carrier \<HH>Pm)" using `m - 1 < length \<HH>` 1(3) unfolding \<HH>Pm_def using comp\<HH>.normal_series_subgroups comp\<GG>.subgroup_finite by auto
    have quots\<GG>notempty:"comp\<GG>.quotients \<noteq> []" using comp\<GG>.quotients_length length by auto
    have quots\<HH>notempty:"comp\<HH>.quotients \<noteq> []" using comp\<HH>.quotients_length length\<HH>big by auto
    
    -- {* Instantiate truncated composition series since they are used for both cases *}
    interpret \<HH>butlast: composition_series \<HH>Pm "take m \<HH>" using comp\<HH>.composition_series_prefix_closed m'(1,2) \<HH>Pm_def by auto
    interpret \<GG>butlast: composition_series \<GG>Pn "take n \<GG>" using comp\<GG>.composition_series_prefix_closed n'(1,2) \<GG>Pn_def by auto
    have ltaken:"n = length (take n \<GG>)" using length_take n'(2) by auto
    have ltakem:"m = length (take m \<HH>)" using length_take m'(2) by auto
    show ?thesis
    proof (cases "\<HH> ! (m - 1)  = \<GG> ! (n - 1)")
      -- {* If \<HH> ! (l - 1) = \<GG> ! 1, everything is simple... *}
      case True
      -- {* The last quotients of $\<GG> and \<HH>$ are equal. *}
      have lasteq:"last comp\<GG>.quotients = last comp\<HH>.quotients"
      proof -
        from length have lg:"length \<GG> - 1 - 1 + 1 = length \<GG> - 1" by (metis Suc_diff_1 Suc_eq_plus1 n'(1) n_def)
        from length\<HH>big have lh:"length \<HH> - 1 - 1 + 1 = length \<HH> - 1" by (metis Suc_diff_1 Suc_eq_plus1 `0 < m` m_def)
        have "last comp\<GG>.quotients = comp\<GG>.quotients ! (length comp\<GG>.quotients - 1)" by (metis last_conv_nth quots\<GG>notempty)
        also have "\<dots> = comp\<GG>.quotients ! (length \<GG> - 1 - 1)" by (metis add_diff_cancel_left' comp\<GG>.quotients_length nat_add_commute)
        also have "\<dots> = G\<lparr>carrier := \<GG> ! ((length \<GG> - 1 - 1) + 1)\<rparr> Mod \<GG> ! (length \<GG> - 1 - 1)"
          unfolding comp\<GG>.quotients_def using length by fastforce
        also have "\<dots> = G\<lparr>carrier := \<GG> ! (length \<GG> - 1)\<rparr> Mod \<GG> ! (n - 1)" using lg unfolding n_def by auto
        also have "\<dots> = G Mod \<HH> ! (m - 1)" using True comp\<GG>.last last_conv_nth comp\<GG>.notempty unfolding m_def by force
        also have "\<dots> = G\<lparr>carrier := \<HH> ! (length \<HH> - 1)\<rparr> Mod \<HH> ! (m - 1)" using comp\<HH>.last last_conv_nth comp\<HH>.notempty by force 
        also have "\<dots> = G\<lparr>carrier := \<HH> ! ((length \<HH> - 1 - 1) + 1)\<rparr> Mod \<HH> ! (length \<HH> - 1 - 1)" using lh unfolding m_def by auto
        also have "\<dots> = comp\<HH>.quotients ! (length \<HH> - 1 - 1)" unfolding comp\<HH>.quotients_def using length\<HH>big by fastforce
        also have "\<dots> = comp\<HH>.quotients ! (length comp\<HH>.quotients - 1)" by (metis calculation comp\<HH>.quotients_length diff_add_inverse nat_add_commute)
        also have "\<dots> = last comp\<HH>.quotients" by (metis last_conv_nth quots\<HH>notempty)
        finally show ?thesis .
      qed
      from ltaken have ind:"multiset_of (map group.iso_class \<GG>butlast.quotients) = multiset_of (map group.iso_class \<HH>butlast.quotients)"
        using 1(1) True n'(5) grp\<GG>Pn.is_group finGbl \<GG>butlast.is_composition_series \<HH>butlast.is_composition_series unfolding \<GG>Pn_def \<HH>Pm_def by metis
      have "multiset_of (map group.iso_class comp\<GG>.quotients)
                    = multiset_of (map group.iso_class (butlast comp\<GG>.quotients @ [last comp\<GG>.quotients]))" by (simp add: quots\<GG>notempty)
      also have "\<dots> = multiset_of (map group.iso_class (\<GG>butlast.quotients @ [last (comp\<GG>.quotients)]))" using comp\<GG>.quotients_butlast length unfolding n_def \<GG>Pn_def by auto
      also have "\<dots> = multiset_of ((map group.iso_class \<GG>butlast.quotients) @ [group.iso_class (last (comp\<GG>.quotients))])" by auto
      also have "\<dots> = multiset_of (map group.iso_class \<GG>butlast.quotients) + {# group.iso_class (last (comp\<GG>.quotients)) #}" by auto
      also have "\<dots> = multiset_of (map group.iso_class \<HH>butlast.quotients) + {# group.iso_class (last (comp\<GG>.quotients)) #}" using ind by simp
      also have "\<dots> = multiset_of (map group.iso_class \<HH>butlast.quotients) + {# group.iso_class (last (comp\<HH>.quotients)) #}" using lasteq by simp
      also have "\<dots> = multiset_of ((map group.iso_class \<HH>butlast.quotients) @ [group.iso_class (last (comp\<HH>.quotients))])" by auto
      also have "\<dots> = multiset_of (map group.iso_class (\<HH>butlast.quotients @ [last (comp\<HH>.quotients)]))" by auto
      also have "\<dots> = multiset_of (map group.iso_class (butlast comp\<HH>.quotients @ [last comp\<HH>.quotients]))" using length\<HH>big comp\<HH>.quotients_butlast unfolding m_def \<HH>Pm_def by auto
      also have "\<dots> = multiset_of (map group.iso_class comp\<HH>.quotients)" using append_butlast_last_id quots\<HH>notempty by simp
      finally show ?thesis .
    next
      case False 
      def \<GG>Pnint\<HH>Pm \<equiv> "G\<lparr>carrier := \<GG> ! (n - 1) \<inter> \<HH> ! (m - 1)\<rparr>"
      have \<GG>Pnmax:"max_normal_subgroup (\<GG> ! (n - 1)) G" unfolding n_def
        by (metis add_lessD1 diff_diff_add n'(3) nat_add_commute one_add_one 1(3) comp\<GG>.snd_to_last_max_normal)
      have \<HH>Pmmax:"max_normal_subgroup (\<HH> ! (m - 1)) G" unfolding m_def
        by (metis add_lessD1 diff_diff_add m'(3) nat_add_commute one_add_one 1(3) comp\<HH>.snd_to_last_max_normal)
      have \<HH>PmnormG:"\<HH> ! (m - 1) \<lhd> G" using comp\<HH>.normal_series_snd_to_last m'(4) unfolding m_def by auto
      have \<GG>PnnormG:"\<GG> ! (n - 1) \<lhd> G" using comp\<GG>.normal_series_snd_to_last n'(6) unfolding n_def by auto
      have \<HH>Pmint\<GG>PnnormG:"\<HH> ! (m - 1) \<inter> \<GG> ! (n - 1) \<lhd> G" using \<HH>PmnormG \<GG>PnnormG by (rule comp\<GG>.normal_subgroup_intersect)
      have \<HH>Pmint\<GG>Pnnorm\<GG>pn:"\<HH> ! (m - 1) \<inter> \<GG> ! (n - 1) \<lhd> \<GG>Pn" using \<GG>PnnormG \<HH>PmnormG Int_lower2 unfolding \<GG>Pn_def
        by (metis comp\<GG>.normal_restrict_supergroup comp\<GG>.normal_series_subgroups comp\<GG>.normal_subgroup_intersect n'(4))
      then interpret grp\<GG>PnMod\<HH>Pmint\<GG>Pn: group "\<GG>Pn Mod \<HH> ! (m - 1) \<inter> \<GG> ! (n - 1)" by (rule normal.factorgroup_is_group)
      have \<HH>Pmint\<GG>Pnnorm\<HH>Pm:"\<HH> ! (m - 1) \<inter> \<GG> ! (n - 1) \<lhd> \<HH>Pm" using \<HH>PmnormG \<GG>PnnormG Int_lower2 Int_commute unfolding \<HH>Pm_def
        by (metis comp\<GG>.normal_restrict_supergroup comp\<GG>.normal_subgroup_intersect comp\<HH>.normal_series_subgroups m'(6))
      then interpret grp\<HH>PmMod\<HH>Pmint\<GG>Pn: group "\<HH>Pm Mod \<HH> ! (m - 1) \<inter> \<GG> ! (n - 1)" by (rule normal.factorgroup_is_group)
      
      -- {* Show that $G / \<HH> ! (m - 1) \<inter> \<GG> ! (n - 1))$ is a simple group. *}

      have "\<GG> ! (n - 1) \<subseteq> (\<HH> ! (m - 1)) <#>\<^bsub>G\<^esub> (\<GG> ! (n - 1))"
        using second_isomorphism_grp.S_contained_in_set_mult \<GG>Pnmax \<HH>PmnormG normal_imp_subgroup
        unfolding second_isomorphism_grp_def second_isomorphism_grp_axioms_def max_normal_subgroup_def by metis
      moreover have "\<GG> ! (n - 1) \<noteq> (\<HH> ! (m - 1)) <#>\<^bsub>G\<^esub> (\<GG> ! (n - 1))" sorry
      ultimately have set_multG:"(\<HH> ! (m - 1)) <#>\<^bsub>G\<^esub> (\<GG> ! (n - 1)) = carrier G" using \<GG>Pnmax \<HH>PmnormG comp\<GG>.normal_subgroup_setmult
        unfolding max_normal_subgroup_def max_normal_subgroup_axioms_def by metis
      then obtain \<phi> where \<phi>:"\<phi> \<in> (\<GG>Pn Mod (\<HH> ! (m - 1) \<inter> \<GG> ! (n - 1))) \<cong> (G\<lparr>carrier := carrier G\<rparr> Mod \<HH> ! (m - 1))"
        using second_isomorphism_grp.normal_intersection_quotient_isom \<HH>PmnormG \<GG>Pnmax normal_imp_subgroup
        unfolding second_isomorphism_grp_def second_isomorphism_grp_axioms_def max_normal_subgroup_def \<GG>Pn_def by metis
      then obtain \<phi>2 where \<phi>2:"\<phi>2 \<in> (G Mod \<HH> ! (m - 1)) \<cong> (\<GG>Pn Mod (\<HH> ! (m - 1) \<inter> \<GG> ! (n - 1)))"
        using group.iso_sym grp\<GG>PnMod\<HH>Pmint\<GG>Pn.is_group by auto
      moreover have "simple_group (G\<lparr>carrier := \<HH> ! (m - 1 + 1)\<rparr> Mod \<HH> ! (m - 1))" using comp\<HH>.simplefact m'(3) by simp
      hence "simple_group (G Mod \<HH> ! (m - 1))" using comp\<HH>.last last_conv_nth comp\<HH>.notempty m'(5) by fastforce
      ultimately have "simple_group (\<GG>Pn Mod (\<HH> ! (m - 1) \<inter> \<GG> ! (n - 1)))"
        using simple_group.iso_simple grp\<GG>PnMod\<HH>Pmint\<GG>Pn.is_group by auto

      -- {* Show analogues of the previous statements for $\<HH> ! (m - 1)$ instead of $\<GG> ! (n - 1)$. *}
      have "\<HH> ! (m - 1) \<subseteq> (\<GG> ! (n - 1)) <#>\<^bsub>G\<^esub> (\<HH> ! (m - 1))"
        using second_isomorphism_grp.S_contained_in_set_mult \<GG>Pnmax \<HH>PmnormG normal_imp_subgroup
        unfolding second_isomorphism_grp_def second_isomorphism_grp_axioms_def max_normal_subgroup_def by metis
      moreover have "\<HH> ! (m - 1) \<noteq> (\<GG> ! (n - 1)) <#>\<^bsub>G\<^esub> (\<HH> ! (m - 1))" sorry
      ultimately have set_multG:"(\<GG> ! (n - 1)) <#>\<^bsub>G\<^esub> (\<HH> ! (m - 1)) = carrier G" using \<HH>Pmmax \<GG>PnnormG comp\<GG>.normal_subgroup_setmult
        unfolding max_normal_subgroup_def max_normal_subgroup_axioms_def by metis
      from set_multG obtain \<psi> where \<psi>:"\<psi> \<in> (\<HH>Pm Mod (\<GG> ! (n - 1) \<inter> \<HH> ! (m - 1))) \<cong> (G\<lparr>carrier := carrier G\<rparr> Mod \<GG> ! (n - 1))"
        using second_isomorphism_grp.normal_intersection_quotient_isom \<GG>PnnormG \<HH>Pmmax normal_imp_subgroup
        unfolding second_isomorphism_grp_def second_isomorphism_grp_axioms_def max_normal_subgroup_def \<HH>Pm_def by metis
      hence "\<psi> \<in> (\<HH>Pm Mod (\<HH> ! (m - 1) \<inter> (\<GG> ! (n - 1)))) \<cong> (G\<lparr>carrier := carrier G\<rparr> Mod \<GG> ! (n - 1))" using Int_commute by metis
      then obtain \<psi>2 where \<psi>2:"\<psi>2 \<in> (G Mod \<GG> ! (n - 1)) \<cong> (\<HH>Pm Mod (\<HH> ! (m - 1) \<inter> \<GG> ! (n - 1)))"
        using group.iso_sym grp\<HH>PmMod\<HH>Pmint\<GG>Pn.is_group by auto
      moreover have "simple_group (G\<lparr>carrier := \<GG> ! (n - 1 + 1)\<rparr> Mod \<GG> ! (n - 1))" using comp\<GG>.simplefact n'(3) by simp
      hence "simple_group (G Mod \<GG> ! (n - 1))" using comp\<GG>.last last_conv_nth comp\<GG>.notempty n'(7) by fastforce
      ultimately have "simple_group (\<HH>Pm Mod (\<HH> ! (m - 1) \<inter> \<GG> ! (n - 1)))" 
        using simple_group.iso_simple grp\<HH>PmMod\<HH>Pmint\<GG>Pn.is_group by auto      
      
      -- {* Instantiate several composition series used to build up the equality of quotient multisets. *}
      def \<KK> \<equiv> "remdups_adj (map (op \<inter> (\<HH> ! (m - 1))) \<GG>)"
      def \<LL> \<equiv> "remdups_adj (map (op \<inter> (\<GG> ! (n - 1))) \<HH>)"
      interpret \<KK>: composition_series \<HH>Pm \<KK> using comp\<GG>.intersect_normal 1(3) \<HH>PmnormG unfolding \<KK>_def \<HH>Pm_def by auto
      interpret \<LL>: composition_series \<GG>Pn \<LL> using comp\<HH>.intersect_normal 1(3) \<GG>PnnormG unfolding \<LL>_def \<GG>Pn_def by auto

      from m'(2) have "Suc (length (take m \<HH>)) \<le> length \<HH>" by auto
      hence multisets\<HH>butlast\<KK>:"multiset_of (map group.iso_class \<HH>butlast.quotients) = multiset_of (map group.iso_class \<KK>.quotients)"
        using  "1.hyps" grp\<HH>Pm.is_group finHbl \<HH>butlast.is_composition_series \<KK>.is_composition_series sorry (* UGH!!! *)
      hence length\<KK>:"m = length \<KK>" using \<HH>butlast.quotients_length \<KK>.quotients_length length_map size_multiset_of ltakem by metis
      hence  "length \<KK> - 1 > 0" "length \<KK> - 1 \<le> length \<KK>" using m'(4) length\<HH>big by auto
      moreover have "\<GG>Pnint\<HH>Pm = (\<HH>Pm\<lparr>carrier := \<KK> ! (length \<KK> - 1 - 1)\<rparr>)" sorry
      ultimately interpret \<KK>butlast: composition_series \<GG>Pnint\<HH>Pm "take (length \<KK> - 1) \<KK>" using \<KK>.composition_series_prefix_closed by metis

      from n'(2) have "Suc (length (take n \<GG>)) \<le> length \<GG>" by auto
      hence multisets\<GG>butlast\<LL>:"multiset_of (map group.iso_class \<GG>butlast.quotients) = multiset_of (map group.iso_class \<LL>.quotients)"
        using  "1.hyps" grp\<GG>Pn.is_group finGbl \<GG>butlast.is_composition_series \<LL>.is_composition_series by metis
      hence length\<LL>:"n = length \<LL>" using \<GG>butlast.quotients_length \<LL>.quotients_length length_map size_multiset_of ltaken by metis
      hence "length \<LL> - 1 > 0" "length \<LL> - 1 \<le> length \<LL>" using n'(6) length by auto
      moreover have "\<GG>Pnint\<HH>Pm = (\<GG>Pn\<lparr>carrier := \<LL> ! (length \<LL> - 1 - 1)\<rparr>)" sorry
      ultimately interpret \<LL>butlast: composition_series \<GG>Pnint\<HH>Pm "take (length \<LL> - 1) \<LL>" using \<LL>.composition_series_prefix_closed by metis

      interpret \<KK>butlastadd\<GG>Pn: composition_series \<GG>Pn "(take (length \<KK> - 1) \<KK>) @ [\<GG> ! (n - 1)]" sorry
      interpret \<LL>butlastadd\<HH>Pm: composition_series \<HH>Pm "(take (length \<LL> - 1) \<LL>) @ [\<HH> ! (m - 1)]" sorry
      
      -- {* Prove equality of those composition series. *}
      have "multiset_of (map group.iso_class comp\<GG>.quotients)
              = multiset_of (map group.iso_class \<GG>butlast.quotients) + {# group.iso_class (G Mod \<GG> ! (n - 1)) #}" sorry
      also have "\<dots> = multiset_of (map group.iso_class \<KK>.quotients) + {# group.iso_class (G Mod \<GG> ! (n - 1)) #}" sorry
      also have "\<dots> = multiset_of (map group.iso_class \<KK>butlast.quotients) + {# group.iso_class (G Mod \<GG> ! (n - 1)), group.iso_class (\<GG>Pn Mod \<GG> ! (n - 1) \<inter> \<HH> ! (m - 1)) #}" sorry
      also have "\<dots> = multiset_of (map group.iso_class \<LL>butlast.quotients) + {# group.iso_class (G Mod \<GG> ! (n - 1)), group.iso_class (\<GG>Pn Mod \<GG> ! (n - 1) \<inter> \<HH> ! (m - 1)) #}" sorry
      also have "\<dots> = multiset_of (map group.iso_class \<LL>butlast.quotients) + {# group.iso_class (G Mod \<HH> ! (m - 1)), group.iso_class (\<HH>Pm Mod \<GG> ! (n - 1) \<inter> \<HH> ! (m - 1)) #}" sorry
      also have "\<dots> = multiset_of (map group.iso_class \<LL>.quotients) + {# group.iso_class (G Mod \<HH> ! (m - 1)) #}" sorry
      also have "\<dots> = multiset_of (map group.iso_class \<HH>butlast.quotients) + {# group.iso_class (G Mod \<HH> ! (m - 1)) #}" sorry
      also have "\<dots> = multiset_of (map group.iso_class comp\<HH>.quotients)" sorry
      finally show ?thesis .
    qed
  qed
qed

text {* As a corollary, we see that the composition series of a fixed group
all have the same length. *}

corollary (in jordan_hoelder) jordan_hoelder_size:
  shows "length \<GG> = length \<HH>"
proof -
  have "length \<GG> = length comp\<GG>.quotients + 1" by (metis comp\<GG>.quotients_length)
  also have "\<dots> = length (map group.iso_class comp\<GG>.quotients) + 1" by (metis length_map)
  also have "\<dots> = size (multiset_of (map group.iso_class comp\<GG>.quotients)) + 1" by (metis size_multiset_of)
  also have "\<dots> = size (multiset_of (map group.iso_class comp\<HH>.quotients)) + 1"
    using jordan_hoelder_multisets is_group finite is_composition_series comp\<HH>.is_composition_series by metis
  also have "\<dots> = length (map group.iso_class comp\<HH>.quotients) + 1" by (metis size_multiset_of)
  also have "\<dots> = length comp\<HH>.quotients + 1" by (metis length_map)
  also have "\<dots> = length \<HH>" by (metis comp\<HH>.quotients_length)
  finally show ?thesis.
qed

end
