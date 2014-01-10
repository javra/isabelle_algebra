(*  Title:      CompositionSeries.thy
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
*)

theory CompositionSeries
imports  "~~/src/HOL/Algebra/Ideal"
  "~~/src/HOL/Algebra/Group"
  "~~/src/HOL/Algebra/IntRing"
  "~~/src/HOL/Algebra/Bij"
  "~~/src/HOL/Algebra/Sylow"
  "~~/src/HOL/Algebra/Coset"
  "~~/src/HOL/Hilbert_Choice"
  "SndSylow"
begin

section{*Preliminaries*}

lemma (in subgroup) subgroup_of_restricted_group:
  assumes "subgroup U (G\<lparr> carrier := H\<rparr>)"
  shows "U \<subseteq> H"
using assms subgroup_imp_subset by force

lemma (in subgroup) subgroup_of_subgroup:
  assumes "group G"
  assumes "subgroup U (G\<lparr> carrier := H\<rparr>)"
  shows "subgroup U G"
proof
  from assms(2) have "U \<subseteq> H" by (rule subgroup_of_restricted_group)
  thus "U \<subseteq> carrier G" by (auto simp:subset)
next
  fix x y
  have a:"x \<otimes> y = x \<otimes>\<^bsub>G\<lparr> carrier := H\<rparr>\<^esub> y" by simp
  assume "x \<in> U" "y \<in> U"
  with assms a show " x \<otimes> y \<in> U" by (metis subgroup.m_closed)
next
  have "\<one>\<^bsub>G\<lparr> carrier := H\<rparr>\<^esub> = \<one>" by simp
  with assms show "\<one> \<in> U" by (metis subgroup.one_closed)
next
  have "subgroup H G"..
  fix x
  assume "x \<in> U"
  with assms(2) have "inv\<^bsub>G\<lparr> carrier := H\<rparr>\<^esub> x \<in> U" by (rule subgroup.m_inv_closed)
  moreover from assms `x \<in> U` have "x \<in> H" by (metis in_mono subgroup_of_restricted_group)
  with assms(1) `subgroup H G` have "inv\<^bsub>G\<lparr> carrier := H\<rparr>\<^esub> x = inv x" by (rule group.subgroup_inv_equality)
  ultimately show "inv x \<in> U" by simp
qed

(* The trivial subgroup is, indeed, a subgroup *)
lemma (in group) triv_subgroup:
  shows "subgroup {\<one>} G"
unfolding subgroup_def by auto

(*The cardinality of the right cosets of the trivial subgroup is the cardinality of the group itself.*)
lemma (in group) card_rcosets_triv:
  assumes finite:"finite (carrier G)"
  shows "card (rcosets {\<one>}) = order G"
proof -
  have "subgroup {\<one>} G" by (rule triv_subgroup)
  with finite have "card (rcosets {\<one>}) * card {\<one>} = order G" by (rule lagrange)
  thus ?thesis by (auto simp:card_Suc_eq)
qed

(*A subgroup which is unique in cardinality is normal*)
lemma (in group) unique_sizes_subgrp_normal:
  assumes fin:"finite (carrier G)"
  assumes "\<exists>!Q. Q \<in> subgroups_of_size q"
  shows "(THE Q. Q \<in> subgroups_of_size q) \<lhd> G"
proof -
  from assms obtain Q where "Q \<in> subgroups_of_size q" by auto
  def Q \<equiv> "THE Q. Q \<in> subgroups_of_size q"
  with assms have Qsize:"Q \<in> subgroups_of_size q" using theI by metis
  hence QG:"subgroup Q G" and cardQ:"card Q = q" unfolding subgroups_of_size_def by auto
  from QG have "Q \<lhd> G" apply(rule normalI)
  proof
    fix g
    assume g:"g \<in> carrier G"
    hence invg:"inv g \<in> carrier G" by (metis inv_closed)
    with fin Qsize have "conjugation_action q (inv g) Q \<in> subgroups_of_size q" by (metis conjugation_is_size_invariant)
    with g Qsize have "(inv g) <# (Q #> inv (inv g)) \<in> subgroups_of_size q" unfolding conjugation_action_def by auto
    with invg g have "inv g <# (Q #> g) = Q" by (metis Qsize assms(2) inv_inv)
    with QG QG g show "Q #> g = g <# Q" by (rule conj_wo_inv)
  qed
  with Q_def show ?thesis by simp
qed

(*A group whose order is the product of two distinct primes p and q where p < q 
has a unique subgroup of size q*)
lemma (in group) pq_order_unique_subgrp:
  assumes finite:"finite (carrier G)"
  assumes orderG:"order G = q * p"
  assumes primep:"prime p" and primeq:"prime q" and pq:"p < q"
  shows "\<exists>!Q. Q \<in> (subgroups_of_size q)"
proof -
  from primep primeq pq have nqdvdp:"\<not> (q dvd p)" by (metis less_not_refl3 prime_def)
  def calM \<equiv> "{s. s \<subseteq> carrier G \<and> card s = q ^ 1}"
  def RelM \<equiv> "{(N1, N2). N1 \<in> calM \<and> N2 \<in> calM \<and> (\<exists>g\<in>carrier G. N1 = N2 #> g)}"
  interpret syl: snd_sylow G q 1 p calM RelM
    unfolding snd_sylow_def sylow_def snd_sylow_axioms_def sylow_axioms_def
    using is_group primeq orderG finite nqdvdp calM_def RelM_def by auto
  obtain Q where Q:"Q \<in> subgroups_of_size q" by (metis (lifting, mono_tags) mem_Collect_eq power_one_right subgroups_of_size_def syl.sylow_thm)
  thus ?thesis 
  proof (rule ex1I)
     fix P
     assume P:"P \<in> subgroups_of_size q"
     have "card (subgroups_of_size q) mod q = 1" by (metis power_one_right syl.p_sylow_mod_p)     
     moreover have "card (subgroups_of_size q) dvd p" by (metis power_one_right syl.num_sylow_dvd_remainder)
     ultimately have "card (subgroups_of_size q) = 1" using pq primep by (metis Divides.mod_less prime_def)
     with Q P show "P = Q" by (auto simp:card_Suc_eq)
  qed
qed

(*This unique subgroup is normal*)
corollary (in group) pq_order_subgrp_normal:
  assumes finite:"finite (carrier G)"
  assumes orderG:"order G = q * p"
  assumes primep:"prime p" and primeq:"prime q" and pq:"p < q"
  shows "(THE Q. Q \<in> subgroups_of_size q) \<lhd> G"
using assms by (metis pq_order_unique_subgrp unique_sizes_subgrp_normal)

(*The trivial subgroup is normal in every group*)
lemma (in group) trivial_subgroup_is_normal:
  shows "{\<one>} \<lhd> G"
unfolding normal_def normal_axioms_def r_coset_def l_coset_def by (auto intro: normalI subgroupI simp: is_group)

section{*Simple Groups*}

locale simple_group = group +
  assumes "order G > 1"
  assumes "\<And>H. H \<lhd> G \<Longrightarrow> (H = carrier G \<or> H = {\<one>})"

lemma (in simple_group) is_simple_group: "simple_group G" by (rule simple_group_axioms)

(*Every group of prime order is simple*)

lemma (in group) prime_order_simple:
  assumes prime:"prime (order G)"
  shows "simple_group G"
proof
  from prime show "1 < order G" unfolding prime_def by auto
next
  fix H
  assume "H \<lhd> G"
  hence HG:"subgroup H G" unfolding normal_def by simp
  hence "card H dvd order G" by (rule card_subgrp_dvd)
  with prime have "card H = 1 \<or> card H = order G" unfolding prime_def by simp
  thus "H = carrier G \<or> H = {\<one>}"
  proof
    assume "card H = 1"
    moreover from HG have "\<one> \<in> H" by (metis subgroup.one_closed)
    ultimately show ?thesis by (auto simp: card_Suc_eq)
  next
    assume "card H = order G"
    moreover from HG have "H \<subseteq> carrier G" unfolding subgroup_def by simp
    moreover from prime have "card (carrier G) > 1" unfolding order_def prime_def..
    hence "finite (carrier G)" by (auto simp:card_ge_0_finite)
    ultimately show ?thesis unfolding order_def by (metis card_eq_subset_imp_eq)
  qed
qed

section{*Normal Series*}

locale normal_series = group +
  fixes \<GG>
  assumes notempty:"\<GG> \<noteq> []"
  assumes hd:"hd \<GG> = {\<one>}"
  assumes last:"last \<GG> = carrier G"
  assumes normal:"\<And>i. i + 1 < length \<GG> \<Longrightarrow> (\<GG> ! i) \<lhd> G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>"

lemma (in normal_series) is_normal_series: "normal_series G \<GG>" by (rule normal_series_axioms)

(*For every group there is a "trivial" normal series consisting only of the group
itself and its trivial subgroup*)
lemma (in group) trivial_normal_series:
  shows "normal_series G [{\<one>}, carrier G]"
unfolding normal_series_def normal_series_axioms_def
using is_group trivial_subgroup_is_normal by auto

lemma (in group) expand_normal_series:
  assumes normal:"normal_series (G\<lparr>carrier := H\<rparr>) \<HH>"
  assumes HG:"H \<lhd> G"
  shows "normal_series G (\<HH> @ [carrier G])"
proof -
  from normal interpret normalH: normal_series "(G\<lparr>carrier := H\<rparr>)" \<HH>.
  from normalH.hd have "hd \<HH> = {\<one>}" by simp
  with normalH.notempty have hdTriv:"hd (\<HH> @ [carrier G]) = {\<one>}" by (metis hd_append2)
  show ?thesis unfolding normal_series_def normal_series_axioms_def using is_group
  proof auto
    fix x
    assume "x \<in> hd (\<HH> @ [carrier G])"
    with hdTriv show "x = \<one>" by simp
  next
    from hdTriv show  "\<one> \<in> hd (\<HH> @ [carrier G])" by simp
  next
    fix i
    assume i:"i < length \<HH>"
    show "(\<HH> @ [carrier G]) ! i \<lhd> G\<lparr>carrier := (\<HH> @ [carrier G]) ! Suc i\<rparr>"
    proof (cases "i + 1 < length \<HH>")
      case True
      with normalH.normal have "\<HH> ! i \<lhd> G\<lparr>carrier := \<HH> ! (i + 1)\<rparr>" by auto
      with i have "(\<HH> @ [carrier G]) ! i \<lhd> G\<lparr>carrier := \<HH> ! (i + 1)\<rparr>" using nth_append by metis
      with True show "(\<HH> @ [carrier G]) ! i \<lhd> G\<lparr>carrier := (\<HH> @ [carrier G]) ! (Suc i)\<rparr>" using nth_append Suc_eq_plus1 by metis
    next
      case False
      with i have i2:"i + 1 = length \<HH>" by simp
      from i have "(\<HH> @ [carrier G]) ! i = \<HH> ! i" by (metis nth_append)
      also from i2 normalH.notempty have "... = last \<HH>" by (metis add_diff_cancel_right' last_conv_nth)
      also from normalH.last have "... = H" by simp
      finally have "(\<HH> @ [carrier G]) ! i = H".
      moreover from i2 have "(\<HH> @ [carrier G]) ! (i + 1) = carrier G" by (metis nth_append_length)
      ultimately show ?thesis using HG by auto
    qed
  qed
qed

lemma (in group) pq_order_normal_series:
  assumes finite:"finite (carrier G)"
  assumes orderG:"order G = q * p"
  assumes primep:"prime p" and primeq:"prime q" and pq:"p < q"
  shows "normal_series G [{\<one>}, (THE H. H \<in> subgroups_of_size q), carrier G]"
proof -
  def H \<equiv> "(THE H. H \<in> subgroups_of_size q)"
  with assms have HG:"H \<lhd> G" by (metis pq_order_subgrp_normal)
  then interpret groupH: group "G\<lparr>carrier := H\<rparr>" unfolding normal_def by (metis subgroup_imp_group)
  have "normal_series (G\<lparr>carrier := H\<rparr>) [{\<one>}, H]"  using groupH.trivial_normal_series by auto
  with HG show ?thesis unfolding H_def by (metis append_Cons append_Nil expand_normal_series)
qed

section{*Composition Series*}

(*A composition series is a normal series where all consecutie factor groups are simple*)
locale composition_series = normal_series +
  assumes "\<And>i. i + 1 <  length \<GG> \<Longrightarrow> simple_group (G\<lparr>carrier := \<GG> ! (i + 1)\<rparr> Mod \<GG> ! i)"

lemma (in composition_series) is_composition_series:
  shows "composition_series G \<GG>"
by (rule composition_series_axioms)

lemma (in group) pq_order_composition_series:
  assumes finite:"finite (carrier G)"
  assumes orderG:"order G = q * p"
  assumes primep:"prime p" and primeq:"prime q" and pq:"p < q"
  shows "composition_series G [{\<one>}, (THE H. H \<in> subgroups_of_size q), carrier G]"
unfolding composition_series_def composition_series_axioms_def
apply(auto)
using assms apply(rule pq_order_normal_series)
proof -
  def H \<equiv> "THE H. H \<in> subgroups_of_size q"
  from assms have exi:"\<exists>!Q. Q \<in> (subgroups_of_size q)" by (auto simp: pq_order_unique_subgrp)
  hence Hsize:"H \<in> subgroups_of_size q" unfolding H_def using theI' by metis
  hence HsubG:"subgroup H G" unfolding subgroups_of_size_def by auto
  then interpret Hgroup: group "G\<lparr>carrier := H\<rparr>" by (metis subgroup_imp_group)
  fix i
  assume "i < Suc (Suc 0)"
  hence "i = 0 \<or> i = 1" by auto
  thus "simple_group (G\<lparr>carrier := [H, carrier G] ! i\<rparr> Mod [{\<one>}, H, carrier G] ! i)"
  proof
    assume i:"i = 0"
    from Hsize have orderH:"order (G\<lparr>carrier := H\<rparr>) = q" unfolding subgroups_of_size_def order_def by simp
    hence "order (G\<lparr>carrier := H\<rparr> Mod {\<one>}) = q" unfolding FactGroup_def using card_rcosets_triv order_def
      by (metis Hgroup.card_rcosets_triv monoid.cases_scheme monoid.select_convs(2) partial_object.select_convs(1) partial_object.update_convs(1))
    have "normal {\<one>} (G\<lparr>carrier := H\<rparr>)" by (metis Hgroup.is_group Hgroup.normal_inv_iff HsubG group.trivial_subgroup_is_normal is_group singleton_iff subgroup.one_closed subgroup.subgroup_of_subgroup)
    hence "group (G\<lparr>carrier := H\<rparr> Mod {\<one>})" by (metis normal.factorgroup_is_group)
    with orderH primeq have "simple_group (G\<lparr>carrier := H\<rparr> Mod {\<one>})" by (metis `order (G\<lparr>carrier := H\<rparr> Mod {\<one>}) = q` group.prime_order_simple)
    with i show ?thesis by simp
  next
    assume i:"i = 1"
    from assms exi have "H \<lhd> G" unfolding H_def by (metis pq_order_subgrp_normal)
    hence groupGH:"group (G Mod H)" by (metis normal.factorgroup_is_group)
    from primeq have "q \<noteq> 0" by (metis prime_0)
    from HsubG finite orderG have "card (rcosets H) * card H = q * p" unfolding subgroups_of_size_def using lagrange by simp
    with Hsize have "card (rcosets H) * q = q * p" unfolding subgroups_of_size_def by simp
    with `q \<noteq> 0` have "card (rcosets H) = p" by auto
    hence "order (G Mod H) = p" unfolding order_def FactGroup_def by auto
    with groupGH primep have "simple_group (G Mod H)" by (metis group.prime_order_simple)
    with i show ?thesis by auto
  qed
qed

end
