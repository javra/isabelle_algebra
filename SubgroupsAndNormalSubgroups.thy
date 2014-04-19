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

text {* An isomorphism restricts to an isomorphism of subgroups. *}

lemma iso_restrict:
  assumes groups:"group G" "group F"
  assumes HG:"subgroup H G"
  assumes \<phi>:"\<phi> \<in> G \<cong> F"
  shows "(restrict \<phi> H) \<in> (G\<lparr>carrier := H\<rparr>) \<cong> (F\<lparr>carrier := \<phi> ` H\<rparr>)"
unfolding iso_def hom_def bij_betw_def inj_on_def
proof auto
  fix g h
  assume "g \<in> H" "h \<in> H"
  hence "g \<in> carrier G" "h \<in> carrier G" by (metis HG subgroup.mem_carrier)+
  thus "\<phi> (g \<otimes>\<^bsub>G\<^esub> h) = \<phi> g \<otimes>\<^bsub>F\<^esub> \<phi> h" using \<phi> unfolding iso_def hom_def by auto
next
  fix g h
  assume "g \<in> H" "h \<in> H" "g \<otimes>\<^bsub>G\<^esub> h \<notin> H"
  hence "False" using HG unfolding subgroup_def by auto
  thus "undefined = \<phi> g \<otimes>\<^bsub>F\<^esub> \<phi> h" by auto
next
  fix g h
  assume g:"g \<in> H" and h:"h \<in> H" and eq:"\<phi> g = \<phi> h"
  hence "g \<in> carrier G" "h \<in> carrier G" by (metis HG subgroup.mem_carrier)+
  with eq show "g = h" using \<phi> unfolding iso_def bij_betw_def inj_on_def by auto
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

section  {* Flattening the type of group carriers *}

text {* Flattening here means to convert the type of group elements from 'a set to 'a.
This is possible whenever the empty set is not an element of the group. *}

definition flatten where
  "flatten (G::('a set, 'b) monoid_scheme) rep = \<lparr>carrier=(rep ` (carrier G)),
      mult=(\<lambda> x y. rep ((the_inv_into (carrier G) rep x) \<otimes>\<^bsub>G\<^esub> (the_inv_into (carrier G) rep y))), one=rep \<one>\<^bsub>G\<^esub> \<rparr>"

lemma flatten_set_group_hom:
  assumes group:"group G"
  assumes inj:"inj_on rep (carrier G)"
  shows "rep \<in> hom G (flatten G rep)"
unfolding hom_def
proof auto
  fix g
  assume g:"g \<in> carrier G"
  thus "rep g \<in> carrier (flatten G rep)" unfolding flatten_def by auto
next
  fix g h
  assume g:"g \<in> carrier G" and h:"h \<in> carrier G"
  hence "rep g \<in> carrier (flatten G rep)" "rep h \<in> carrier (flatten G rep)" unfolding flatten_def by auto
  hence "rep g \<otimes>\<^bsub>flatten G rep\<^esub> rep h
    = rep (the_inv_into (carrier G) rep (rep g) \<otimes>\<^bsub>G\<^esub> the_inv_into (carrier G) rep (rep h))" unfolding flatten_def by auto
  also have "\<dots> = rep (g \<otimes>\<^bsub>G\<^esub> h)" using inj g h by (metis the_inv_into_f_f)
  finally show "rep (g \<otimes>\<^bsub>G\<^esub> h) = rep g \<otimes>\<^bsub>flatten G rep\<^esub> rep h"..
qed

lemma flatten_set_group:
  assumes group:"group G"
  assumes inj:"inj_on rep (carrier G)"
  shows "group (flatten G rep)"
proof (rule groupI)
  fix x y
  assume x:"x \<in> carrier (flatten G rep)" and y:"y \<in> carrier (flatten G rep)"
  def g \<equiv> "the_inv_into (carrier G) rep x" and h \<equiv> "the_inv_into (carrier G) rep y"
  hence "x \<otimes>\<^bsub>flatten G rep\<^esub> y = rep (g \<otimes>\<^bsub>G\<^esub> h)" unfolding flatten_def by auto
  moreover from g_def h_def have "g \<in> carrier G" "h \<in> carrier G" 
    using inj x y the_inv_into_into unfolding flatten_def by (metis partial_object.select_convs(1) subset_refl)+
  hence "g \<otimes>\<^bsub>G\<^esub> h \<in> carrier G" by (metis group group.is_monoid monoid.m_closed)
  hence "rep (g \<otimes>\<^bsub>G\<^esub> h) \<in> carrier (flatten G rep)" unfolding flatten_def by simp
  ultimately show "x \<otimes>\<^bsub>flatten G rep\<^esub> y \<in> carrier (flatten G rep)" by simp
next
  show "\<one>\<^bsub>flatten G rep\<^esub> \<in> carrier (flatten G rep)" unfolding flatten_def by (simp add: group group.is_monoid)
next
  fix x y z
  assume x:"x \<in> carrier (flatten G rep)" and y:"y \<in> carrier (flatten G rep)" and z:"z \<in> carrier (flatten G rep)"
  def g \<equiv> "the_inv_into (carrier G) rep x" and h \<equiv> "the_inv_into (carrier G) rep y" and k \<equiv> "the_inv_into (carrier G) rep z"
  hence "x \<otimes>\<^bsub>flatten G rep\<^esub> y \<otimes>\<^bsub>flatten G rep\<^esub> z = (rep (g \<otimes>\<^bsub>G\<^esub> h)) \<otimes> \<^bsub>flatten G rep\<^esub> z" unfolding flatten_def by auto
  also have "\<dots> = rep (the_inv_into (carrier G) rep (rep (g \<otimes>\<^bsub>G\<^esub> h)) \<otimes>\<^bsub>G\<^esub> k)" using k_def unfolding flatten_def by auto
  also from g_def h_def k_def have ghkG:"g \<in> carrier G" "h \<in> carrier G" "k \<in> carrier G"
    using inj x y z the_inv_into_into unfolding flatten_def by fastforce+
  hence gh:"g \<otimes>\<^bsub>G\<^esub> h \<in> carrier G" and hk:"h \<otimes>\<^bsub>G\<^esub> k \<in> carrier G" by (metis group group.is_monoid monoid.m_closed)+
  hence "rep (the_inv_into (carrier G) rep (rep (g \<otimes>\<^bsub>G\<^esub> h)) \<otimes>\<^bsub>G\<^esub> k) = rep ((g \<otimes>\<^bsub>G\<^esub> h) \<otimes>\<^bsub>G\<^esub> k)"
    unfolding flatten_def using inj the_inv_into_f_f by fastforce
  also have "\<dots> = rep (g \<otimes>\<^bsub>G\<^esub> (h \<otimes>\<^bsub>G\<^esub> k))" using group group.is_monoid ghkG monoid.m_assoc by fastforce
  also have "\<dots> = x \<otimes>\<^bsub>flatten G rep\<^esub> (rep (h \<otimes>\<^bsub>G\<^esub> k))" unfolding g_def flatten_def using hk inj the_inv_into_f_f by fastforce
  also have "\<dots> = x \<otimes>\<^bsub>flatten G rep\<^esub> (y \<otimes>\<^bsub>flatten G rep\<^esub> z)" unfolding h_def k_def flatten_def using x y by force
  finally show "x \<otimes>\<^bsub>flatten G rep\<^esub> y \<otimes>\<^bsub>flatten G rep\<^esub> z = x \<otimes>\<^bsub>flatten G rep\<^esub> (y \<otimes>\<^bsub>flatten G rep\<^esub> z)".
next
  fix x
  assume x:"x \<in> carrier (flatten G rep)"
  def g \<equiv> "the_inv_into (carrier G) rep x"
  hence gG:"g \<in> carrier G" using inj x unfolding flatten_def using the_inv_into_into by force
  have "\<one>\<^bsub>G\<^esub> \<in> (carrier G)" by (simp add: group group.is_monoid)
  hence "the_inv_into (carrier G) rep (\<one>\<^bsub>flatten G rep\<^esub>) = \<one>\<^bsub>G\<^esub>" unfolding flatten_def using the_inv_into_f_f inj by force
  hence "\<one>\<^bsub>flatten G rep\<^esub> \<otimes>\<^bsub>flatten G rep\<^esub> x = rep (\<one>\<^bsub>G\<^esub> \<otimes>\<^bsub>G\<^esub> g)" unfolding flatten_def g_def by simp
  also have "\<dots> = rep g" using gG group by (metis group.is_monoid monoid.l_one)
  also have "\<dots> = x" unfolding g_def using inj x f_the_inv_into_f unfolding flatten_def by force
  finally show "\<one>\<^bsub>flatten G rep\<^esub> \<otimes>\<^bsub>flatten G rep\<^esub> x = x".
next
  from group inj have hom:"rep \<in> hom G (flatten G rep)" using flatten_set_group_hom by auto
  fix x
  assume x:"x \<in> carrier (flatten G rep)"
  def g \<equiv> "the_inv_into (carrier G) rep x"
  hence gG:"g \<in> carrier G" using inj x unfolding flatten_def using the_inv_into_into by force
  hence invG:"inv\<^bsub>G\<^esub> g \<in> carrier G" by (metis group group.inv_closed)
  hence "rep (inv\<^bsub>G\<^esub> g) \<in> carrier (flatten G rep)" unfolding flatten_def by auto
  moreover have "rep (inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>flatten G rep\<^esub> x = rep (inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>flatten G rep\<^esub> (rep g)"
    unfolding g_def using f_the_inv_into_f inj x unfolding flatten_def by fastforce
  hence "rep (inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>flatten G rep\<^esub> x = rep (inv\<^bsub>G\<^esub> g \<otimes>\<^bsub>G\<^esub> g)"
    using hom unfolding hom_def using gG invG hom_def by auto
  hence "rep (inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>flatten G rep\<^esub> x = rep \<one>\<^bsub>G\<^esub>" using invG gG by (metis group group.l_inv)
  hence "rep (inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>flatten G rep\<^esub> x = \<one>\<^bsub>flatten G rep\<^esub>" unfolding flatten_def by auto
  ultimately show "\<exists>y\<in>carrier (flatten G rep). y \<otimes>\<^bsub>flatten G rep\<^esub> x = \<one>\<^bsub>flatten G rep\<^esub>" by auto
qed

lemma (in normal) flatten_set_group_mod_inj:
  shows "inj_on (\<lambda>U. SOME g. g \<in> U) (carrier (G Mod H))"
proof (rule inj_onI)
  fix U V
  assume U:"U \<in> carrier (G Mod H)" and V:"V \<in> carrier (G Mod H)"
  then obtain g h where g:"U = H #> g" "g \<in> carrier G" and h:"V = H #> h" "h \<in> carrier G"
    unfolding FactGroup_def RCOSETS_def by auto
  hence notempty:"U \<noteq> {}" "V \<noteq> {}" by (metis empty_iff is_subgroup rcos_self)+
  assume "(SOME g. g \<in> U) = (SOME g. g \<in> V)"
  with notempty have "(SOME g. g \<in> U) \<in> U \<inter> V" by (metis IntI ex_in_conv someI)
  thus "U = V" by (metis Int_iff g h is_subgroup repr_independence)
qed

lemma (in normal) flatten_set_group_mod:
  shows "group (flatten (G Mod H) (\<lambda>U. SOME g. g \<in> U))"
using factorgroup_is_group flatten_set_group_mod_inj by (rule flatten_set_group)

lemma (in normal) flatten_set_group_mod_iso:
  shows "(\<lambda>U. SOME g. g \<in> U) \<in> (G Mod H) \<cong> (flatten (G Mod H) (\<lambda>U. SOME g. g \<in> U))"
unfolding iso_def bij_betw_def
apply (auto)
 apply (metis flatten_set_group_mod_inj factorgroup_is_group flatten_set_group_hom)
 apply (rule flatten_set_group_mod_inj)
 unfolding flatten_def apply (auto)
done

end
