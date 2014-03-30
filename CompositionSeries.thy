(*  Title:      Composition Series
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
    Maintainer: Jakob von Raumer <jakob.raumer@student.kit.edu>
*)

theory CompositionSeries
imports
  "SndSylow"
begin

section {* Preliminaries *}

lemma bij_betw_inv_subset:
  assumes bij:"bij_betw f A B"
  assumes "N \<subseteq> B"
  shows "f ` ((inv_into A f) ` N) = N"
proof auto
  fix n
  assume n:"n \<in> N"
  show "n \<in> f ` ((inv_into A f) ` N)" using assms image_inv_into_cancel
qed
oops

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

text {* Being a subgroup is preserved by surjective homomorphisms *}

lemma (in subgroup) surj_hom_subgroup:
  assumes \<phi>:"group_hom G F \<phi>"
  assumes \<phi>surj:"\<phi> ` (carrier G) = carrier F"
  shows "subgroup (\<phi> ` H) F"
proof
  from \<phi>surj show img_subset:"\<phi> ` H \<subseteq> carrier F" unfolding iso_def bij_betw_def by auto
next
  fix f f'
	assume h:"f \<in> \<phi> ` H" and h':"f' \<in> \<phi> ` H"
	with \<phi>surj obtain g g' where g:"g \<in> H" "f = \<phi> g" and g':"g' \<in> H" "f' = \<phi> g'" by auto
	hence "g \<otimes>\<^bsub>G\<^esub> g' \<in> H" by (metis m_closed)
  hence "\<phi> (g \<otimes>\<^bsub>G\<^esub> g') \<in> \<phi> ` H" by simp
  with g g' \<phi> show "f \<otimes>\<^bsub>F\<^esub> f' \<in> \<phi> ` H"  using group_hom.hom_mult by fastforce
next
  have "\<phi> \<one> \<in> \<phi> ` H" by auto
  with \<phi> show  "\<one>\<^bsub>F\<^esub> \<in> \<phi> ` H" by (metis group_hom.hom_one)
next
  fix f
  assume f:"f \<in> \<phi> ` H"
  then obtain g where g:"g \<in> H" "f = \<phi> g" by auto
  hence "inv g \<in> H" by auto
  hence "\<phi> (inv g) \<in> \<phi> ` H" by auto
  with \<phi> g subset show "inv\<^bsub>F\<^esub> f \<in> \<phi> ` H" using group_hom.hom_inv by fastforce
qed

text {* ... and thus of course by isomorphisms of groups. *}

lemma iso_subgroup:
  assumes groups:"group G" "group F"
  assumes HG:"subgroup H G"
  assumes \<phi>:"\<phi> \<in> G \<cong> F"
  shows "subgroup (\<phi> ` H) F"
proof -
  from groups \<phi> have "group_hom G F \<phi>" unfolding group_hom_def group_hom_axioms_def iso_def by auto
  moreover from \<phi> have "\<phi> ` (carrier G) = carrier F" unfolding iso_def bij_betw_def by simp
  moreover note HG
  ultimately show ?thesis by (metis subgroup.surj_hom_subgroup)
qed

text {* Being a normal subgroup is preserved by surjective homomorphisms. *}

lemma (in normal) surj_hom_normal_subgroup:
  assumes \<phi>:"group_hom G F \<phi>"
  assumes \<phi>surj:"\<phi> ` (carrier G) = carrier F"
  shows "(\<phi> ` H) \<lhd> F"
proof (rule group.normalI)
  from \<phi> show "group F" unfolding group_hom_def group_hom_axioms_def by simp
next
  from \<phi> \<phi>surj show "subgroup (\<phi> ` H) F" by (rule surj_hom_subgroup)
next
  show "\<forall>x\<in>carrier F. \<phi> ` H #>\<^bsub>F\<^esub> x = x <#\<^bsub>F\<^esub> \<phi> ` H"
  proof
    fix f
    assume f:"f \<in> carrier F"
    with \<phi>surj obtain g where g:"g \<in> carrier G" "f = \<phi> g" by auto
    hence "\<phi> ` H #>\<^bsub>F\<^esub> f = \<phi> ` H #>\<^bsub>F\<^esub> \<phi> g" by simp
    also have "... = (\<lambda>x. (\<phi> x) \<otimes>\<^bsub>F\<^esub> (\<phi> g)) ` H" unfolding r_coset_def image_def by auto
    also have "... = (\<lambda>x. \<phi> (x \<otimes> g)) ` H" using subset g \<phi> group_hom.hom_mult unfolding image_def by fastforce
    also have "... = \<phi> ` (H #> g)" using \<phi> unfolding r_coset_def by auto
    also have "... = \<phi> ` (g <# H)" by (metis coset_eq g(1))
    also have "... = (\<lambda>x. \<phi> (g \<otimes> x)) ` H" using \<phi> unfolding l_coset_def by auto
    also have "... = (\<lambda>x. (\<phi> g) \<otimes>\<^bsub>F\<^esub> (\<phi> x)) ` H" using subset g \<phi> group_hom.hom_mult by fastforce
    also have "... = \<phi> g <#\<^bsub>F\<^esub> \<phi> ` H" unfolding l_coset_def image_def by auto
    also have "... = f <#\<^bsub>F\<^esub> \<phi> ` H" using g by simp
    finally show "\<phi> ` H #>\<^bsub>F\<^esub> f = f <#\<^bsub>F\<^esub> \<phi> ` H".
  qed
qed

text {* Being a normal subgroup is preserved by group isomorphisms. *}

lemma iso_normal_subgroup:
  assumes groups:"group G" "group F"
  assumes HG:"H \<lhd> G"
  assumes \<phi>:"\<phi> \<in> G \<cong> F"
  shows "(\<phi> ` H) \<lhd> F"
proof -
  from groups \<phi> have "group_hom G F \<phi>" unfolding group_hom_def group_hom_axioms_def iso_def by auto
  moreover from \<phi> have "\<phi> ` (carrier G) = carrier F" unfolding iso_def bij_betw_def by simp
  moreover note HG
  ultimately show ?thesis using normal.surj_hom_normal_subgroup by metis
qed

text {* The trivial subgroup is a subgroup: *}

lemma (in group) triv_subgroup:
  shows "subgroup {\<one>} G"
unfolding subgroup_def by auto

text{*The cardinality of the right cosets of the trivial subgroup is the cardinality of the group itself: *}
lemma (in group) card_rcosets_triv:
  assumes "finite (carrier G)"
  shows "card (rcosets {\<one>}) = order G"
proof -
  have "subgroup {\<one>} G" by (rule triv_subgroup)
  with assms have "card (rcosets {\<one>}) * card {\<one>} = order G" by (rule lagrange)
  thus ?thesis by (auto simp:card_Suc_eq)
qed

text{* A subgroup which is unique in cardinality is normal: *}

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

text {* A group whose order is the product of two distinct
primes $p$ and $q$ where $p < q$ has a unique subgroup of size $q$: *}

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

text {* This unique subgroup is normal *}

corollary (in group) pq_order_subgrp_normal:
  assumes finite:"finite (carrier G)"
  assumes orderG:"order G = q * p"
  assumes primep:"prime p" and primeq:"prime q" and pq:"p < q"
  shows "(THE Q. Q \<in> subgroups_of_size q) \<lhd> G"
using assms by (metis pq_order_unique_subgrp unique_sizes_subgrp_normal)

text {* The trivial subgroup is normal in every group *}

lemma (in group) trivial_subgroup_is_normal:
  shows "{\<one>} \<lhd> G"
unfolding normal_def normal_axioms_def r_coset_def l_coset_def by (auto intro: normalI subgroupI simp: is_group)

section {*Simple Groups*}

locale simple_group = group +
  assumes order_gt_one:"order G > 1"
  assumes no_real_normal_subgroup:"\<And>H. H \<lhd> G \<Longrightarrow> (H = carrier G \<or> H = {\<one>})"

lemma (in simple_group) is_simple_group: "simple_group G" by (rule simple_group_axioms)

text {* Every group of prime order is simple *}

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

text {* Being simple is a property that is preserved by isomorphisms. *}

lemma (in simple_group) iso_simple:
  assumes H:"group H"
  assumes iso:"\<phi> \<in> G \<cong> H"
  shows "simple_group H"
unfolding simple_group_def simple_group_axioms_def using assms(1)
proof (auto del: equalityI)
  from iso have "order G = order H" unfolding iso_def order_def using bij_betw_same_card by auto
  with order_gt_one show "Suc 0 < order H" by simp
next
  have inv_iso:"(inv_into (carrier G) \<phi>) \<in> H \<cong> G" using iso by (rule iso_sym)
  fix N
  assume NH:"N \<lhd> H" and Nneq1:"N \<noteq> {\<one>\<^bsub>H\<^esub>}"
  then interpret Nnormal: normal N H by simp
  def M \<equiv> "(inv_into (carrier G) \<phi>) ` N"
  hence MG:"M \<lhd> G" using inv_iso NH H by (metis is_group iso_normal_subgroup)
  from Nneq1 have "M \<noteq> {\<one>}" sorry
  hence "M = carrier G" using no_real_normal_subgroup MG by auto
  moreover have surj:"\<phi> ` carrier G = carrier H" using iso unfolding iso_def bij_betw_def by simp
  hence "\<phi> ` M = N" unfolding M_def using Nnormal.subset image_inv_into_cancel by metis
  ultimately show "N = carrier H" using surj by simp
qed

section{*Normal Series*}

text {* We define a normal series as a locale which fixes one group
@{term G} and a list @{term \<GG>} of subsets of @{term G}'s carrier. This list
must begin with the trivial subgroup, end with the carrier of the group itself
and each of the list items must be a normal subgroup of its successor. *}

locale normal_series = group +
  fixes \<GG>
  assumes notempty:"\<GG> \<noteq> []"
  assumes hd:"hd \<GG> = {\<one>}"
  assumes last:"last \<GG> = carrier G"
  assumes normal:"\<And>i. i + 1 < length \<GG> \<Longrightarrow> (\<GG> ! i) \<lhd> G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>"

lemma (in normal_series) is_normal_series: "normal_series G \<GG>" by (rule normal_series_axioms)

text {* For every group there is a "trivial" normal series consisting
only of the group itself and its trivial subgroup. *}

lemma (in group) trivial_normal_series:
  shows "normal_series G [{\<one>}, carrier G]"
unfolding normal_series_def normal_series_axioms_def
using is_group trivial_subgroup_is_normal by auto

text {* We can also show that the normal series presented above is the only such with
a length of two: *}

lemma (in normal_series) length_two_unique:
  assumes "length \<GG> = 2"
  shows "\<GG> = [{\<one>}, carrier G]"
proof(rule nth_equalityI)
  from assms show "length \<GG> = length [{\<one>}, carrier G]" by auto
next
  show "\<forall>i<length \<GG>. \<GG> ! i = [{\<one>}, carrier G] ! i"
  proof(rule allI, rule impI)
    fix i
    assume i:"i < length \<GG>"
    with assms have "i = 0 \<or> i = 1" by auto
    thus "\<GG> ! i = [{\<one>}, carrier G] ! i"
    proof(rule disjE)
      assume i:"i = 0"
      hence "\<GG> ! i = hd \<GG>" by (metis hd_conv_nth notempty)
      thus "\<GG> ! i = [{\<one>}, carrier G] ! i" using hd i by simp
    next
      assume i:"i = 1"
      with assms have "\<GG> ! i = last \<GG>" by (metis diff_add_inverse last_conv_nth nat_1_add_1 notempty)
      thus "\<GG> ! i = [{\<one>}, carrier G] ! i" using last i by simp
    qed
  qed
qed

text {* We can construct new normal series by expanding existing ones: If we
append the carrier of a group @{term G} to a normal series for a normal subgroup
@{term "H \<lhd> G"} we receive a normal series for @{term G}. *}

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

text {* If a group's order is the product of two distinct primes @{term p} and @{term q}, where
@{term "p < q"}, we can construct a normal series using the only subgroup of size  @{term q}. *}

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

text {* The following defines the list of all quotient groups of the normal_series: *}

definition (in normal_series) quotient_list
  where "quotient_list = map (\<lambda>i. G\<lparr>carrier := \<GG> ! (i + 1)\<rparr> Mod \<GG> ! i) [0..<((length \<GG>) - 1)]"

text {* The list of quotient groups has one less entry than the series itself: *}

lemma (in normal_series) quotient_list_length:
  shows "length quotient_list + 1 = length \<GG>"
proof -
  have "length quotient_list + 1 = length [0..<((length \<GG>) - 1)] + 1" unfolding quotient_list_def by simp
  also have "... = (length \<GG> - 1) + 1" by (metis diff_zero length_upt)
  also with notempty have "... = length \<GG>" by (metis add_eq_if comm_monoid_diff_class.diff_cancel length_0_conv nat_add_commute zero_neq_one)
  finally show ?thesis .
qed

section {* Composition Series *}

text {* A composition series is a normal series where all consecutie factor groups are simple: *}

locale composition_series = normal_series +
  assumes simplefact:"\<And>i. i + 1 <  length \<GG> \<Longrightarrow> simple_group (G\<lparr>carrier := \<GG> ! (i + 1)\<rparr> Mod \<GG> ! i)"

lemma (in composition_series) is_composition_series:
  shows "composition_series G \<GG>"
by (rule composition_series_axioms)

text {* The normal series for groups of order @{term "p * q"} is even a composition series: *}

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
      by (metis Hgroup.card_rcosets_triv HsubG finite monoid.cases_scheme monoid.select_convs(2) partial_object.select_convs(1) partial_object.update_convs(1) subgroup_finite)
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
