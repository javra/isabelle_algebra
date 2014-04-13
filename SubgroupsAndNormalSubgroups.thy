(*  Title:      Additional Facts about Subgroups and Normal Subgroups
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
    Maintainer: Jakob von Raumer <jakob.raumer@student.kit.edu>
*)

theory SubgroupsAndNormalSubgroups
imports
  "Coset"
begin

section {* More Facts about Subgroups *}

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

text {* The intersection of two subgroups is, again, a subgroup *}

lemma (in group) subgroup_intersect:
  assumes "subgroup H G"
  assumes "subgroup H' G"
  shows "subgroup (H \<inter> H') G"
using assms unfolding subgroup_def by auto

section {* Facts about Normal Subgroups *}

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

text {* The cardinality of the right cosets of the trivial subgroup is the cardinality of the group itself: *}

lemma (in group) card_rcosets_triv:
  assumes "finite (carrier G)"
  shows "card (rcosets {\<one>}) = order G"
proof -
  have "subgroup {\<one>} G" by (rule triv_subgroup)
  with assms have "card (rcosets {\<one>}) * card {\<one>} = order G" by (rule lagrange)
  thus ?thesis by (auto simp:card_Suc_eq)
qed

text {* The intersection of two normal subgroups is, again, a normal subgroup. *}

lemma (in group) normal_subgroup_intersect:
  assumes "M \<lhd> G" and "N \<lhd> G"
  shows "M \<inter> N \<lhd> G"
using assms subgroup_intersect is_group normal_inv_iff by simp

end
