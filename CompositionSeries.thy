(*  Title:      Composition Series
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
    Maintainer: Jakob von Raumer <jakob.raumer@student.kit.edu>
*)

theory CompositionSeries
imports
  "SimpleGroups"
begin

section {* Preliminaries *}

text {* A subgroup which is unique in cardinality is normal: *}

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

text {* All entries of a normal series for $G$ are subgroups of $G$. *}

lemma (in normal_series) normal_series_subgroups:
  shows "i < length \<GG> \<Longrightarrow> subgroup (\<GG> ! i) G"
proof -
  have "i + 1 < length \<GG> \<Longrightarrow> subgroup (\<GG> ! i) G"
  proof (induction "length \<GG> - (i + 2)" arbitrary: i)
    case 0
    hence i:"i + 2 = length \<GG>" using assms by simp
    hence ii:"i + 1 = length \<GG> - 1" using assms by force
    from i normal have "\<GG> ! i \<lhd> G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>" by auto
    with ii last notempty show "subgroup (\<GG> ! i) G" using last_conv_nth normal_imp_subgroup by fastforce
  next
    case (Suc k)
    from Suc(3)  normal have i:"subgroup (\<GG> ! i) (G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>)" using normal_imp_subgroup by auto
    from Suc(2) have k:"k = length \<GG> - ((i + 1) + 2)" by arith
    with Suc have "subgroup (\<GG> ! (i + 1)) G" by simp
    with i show "subgroup (\<GG> ! i) G" by (metis is_group subgroup.subgroup_of_subgroup)
  qed
  moreover have "i + 1 = length \<GG> \<Longrightarrow> subgroup (\<GG> ! i) G"
    using last notempty last_conv_nth by (metis add_diff_cancel_right' subgroup_self)
  ultimately show "i < length \<GG> \<Longrightarrow> subgroup (\<GG> ! i) G" by force
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

text {* A composition series for a group $G$ has length one iff $G$ is the trivial group. *}

lemma (in composition_series) composition_series_length_one:
  shows "(length \<GG> = 1) = (\<GG> = [{\<one>}])"
proof
  assume "length \<GG> = 1"
  with hd have "length \<GG> = length [{\<one>}] \<and> (\<forall>i < length \<GG>. \<GG> ! i = [{\<one>}] ! i)" using hd_conv_nth notempty by force
  thus "\<GG> = [{\<one>}]" using list_eq_iff_nth_eq by blast
next
  assume "\<GG> = [{\<one>}]"
  thus "length \<GG> = 1" by simp
qed

lemma (in composition_series) composition_series_triv_group:
  shows "(carrier G = {\<one>}) = (\<GG> = [{\<one>}])"
proof
  assume G:"carrier G = {\<one>}"
  have "length \<GG> = 1"
  proof (rule ccontr)
    assume "length \<GG> \<noteq> 1"
    with notempty have length:"length \<GG> \<ge> 2" by (metis Suc_eq_plus1 length_0_conv less_2_cases not_less plus_nat.add_0)
    with simplefact hd hd_conv_nth notempty have "simple_group (G\<lparr>carrier := \<GG> ! 1\<rparr> Mod {\<one>})" by force
    moreover have SG:"subgroup (\<GG> ! 1) G" using length normal_series_subgroups by auto
    hence "group (G\<lparr>carrier := \<GG> ! 1\<rparr>)" by (metis subgroup_imp_group)
    ultimately have  "simple_group (G\<lparr>carrier := \<GG> ! 1\<rparr>)" using group.trivial_factor_iso simple_group.iso_simple by fastforce
    moreover from SG G have "carrier (G\<lparr>carrier := \<GG> ! 1\<rparr>) = {\<one>}" unfolding subgroup_def by auto
    ultimately show False using simple_group.simple_not_triv by force
  qed
  thus "\<GG> = [{\<one>}]" by (metis composition_series_length_one)
next
  assume "\<GG> = [{\<one>}]"
  with last show "carrier G = {\<one>}" by auto
qed

text {* A composition series of a simple group always is its trivial one. *}

lemma (in composition_series) composition_series_simple_group:
  shows "(simple_group G) = (\<GG> = [{\<one>}, carrier G])"
proof
  assume "\<GG> = [{\<one>}, carrier G]"
  with simplefact have "simple_group (G Mod {\<one>})" by auto
  moreover have "the_elem \<in> (G Mod {\<one>}) \<cong> G" by (rule trivial_factor_iso)
  ultimately show "simple_group G" by (metis is_group simple_group.iso_simple)
next
  assume simple:"simple_group G"
  have "length \<GG> > 1"
  proof (rule ccontr)
    assume "\<not> 1 < length \<GG>"
    hence "length \<GG> = 1" by (metis nat_add_commute nat_less_cases not_add_less1 quotient_list_length) 
    hence "hd \<GG> = last \<GG>" sorry
    hence "carrier G = {\<one>}" using hd last by simp
    hence "order G = 1" unfolding order_def by auto
    with simple show "False" unfolding simple_group_def simple_group_axioms_def by auto
  qed
  moreover have "length \<GG> \<le> 2"
  proof (rule ccontr)
    def k \<equiv> "length \<GG> - 2"
    assume "\<not> (length \<GG> \<le> 2)"
    hence gt2:"length \<GG> > 2" by simp
    hence ksmall:"k + 1 < length \<GG>" unfolding k_def by auto
    from gt2 have carrier:"\<GG> ! (k + 1) = carrier G" using notempty last last_conv_nth k_def
      by (metis Nat.add_diff_assoc Nat.diff_cancel `\<not> length \<GG> \<le> 2` nat_add_commute nat_le_linear one_add_one)
    from normal ksmall have "\<GG> ! k \<lhd> G\<lparr> carrier := \<GG> ! (k + 1)\<rparr>" by simp
    from simplefact ksmall have simplek:"simple_group (G\<lparr>carrier := \<GG> ! (k + 1)\<rparr> Mod \<GG> ! k)" by simp
    from simplefact ksmall have simplek':"simple_group (G\<lparr>carrier := \<GG> ! ((k - 1) + 1)\<rparr> Mod \<GG> ! (k - 1))" by auto
    have "\<GG> ! k \<lhd> G" using carrier k_def gt2 normal ksmall by force
    with simple have "(\<GG> ! k) = carrier G \<or> (\<GG> ! k) = {\<one>}" unfolding simple_group_def simple_group_axioms_def by simp
    thus "False"
    proof (rule disjE)
      assume "\<GG> ! k = carrier G"
      hence "G\<lparr>carrier := \<GG> ! (k + 1)\<rparr> Mod \<GG> ! k = G Mod (carrier G)" using carrier by auto
      with simplek self_factor_not_simple show "False" by auto
    next
      assume "\<GG> ! k = {\<one>}"
      moreover from k_def gt2 have "(k - 1) + 1 = k" by auto
      ultimately have "G\<lparr>carrier := \<GG> ! ((k - 1) + 1)\<rparr> Mod \<GG> ! (k - 1) = G\<lparr>carrier := {\<one>}\<rparr> Mod \<GG> ! (k - 1)" using simplek' by auto
      hence "order (G\<lparr>carrier := \<GG> ! ((k - 1) + 1)\<rparr> Mod \<GG> ! (k - 1)) = 1" unfolding FactGroup_def order_def RCOSETS_def by force
      thus "False" using simplek' unfolding simple_group_def simple_group_axioms_def by auto
    qed
  qed
  ultimately have "length \<GG> = 2" by simp
  thus "\<GG> = [{\<one>}, carrier G]" by (rule length_two_unique)
qed

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
