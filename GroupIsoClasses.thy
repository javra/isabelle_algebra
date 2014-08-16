(*  Title:      Isomorphism Classes of Groups
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
    Maintainer: Jakob von Raumer <jakob.raumer@student.kit.edu>
*)

theory GroupIsoClasses
imports
  "Group"
  "List"
  "Coset"
begin

typedef 'a group = "{G :: 'a monoid. group G}"
proof
  def x \<equiv> "SOME x. True"
  show "\<lparr>carrier = {x}, mult = (\<lambda>x y. x), one = x\<rparr> \<in> {G. group G}"
  unfolding group_def group_axioms_def monoid_def Units_def by auto
qed
print_theorems
find_theorems "Abs_group ?x"
find_theorems "Rep_group ?x"
find_theorems "List.member"


definition group_iso_rel :: "'a group \<Rightarrow> 'a group \<Rightarrow> bool"
  where "group_iso_rel G H = (\<exists>\<phi>. \<phi> \<in> Rep_group G \<cong> Rep_group H)"

quotient_type 'a group_iso_class = "'a group" / group_iso_rel
  morphisms Rep_Integ Abs_Integ
proof (rule equivpI)
  show "reflp group_iso_rel"
  proof (rule reflpI)
    fix G :: "'b group"
    show "group_iso_rel G G"
    unfolding group_iso_rel_def using Rep_group iso_refl by auto
  qed
next
  show "symp group_iso_rel"
  proof (rule sympI)
    fix G H :: "'b group"
    assume "group_iso_rel G H"
    then obtain \<phi> where "\<phi> \<in> Rep_group G \<cong> Rep_group H" unfolding group_iso_rel_def by auto
    then obtain \<phi>' where "\<phi>' \<in> Rep_group H \<cong> Rep_group G" using group.iso_sym Rep_group by fastforce
    thus "group_iso_rel H G" unfolding group_iso_rel_def by auto
  qed
next
  show "transp group_iso_rel" 
  proof (rule transpI)
    fix G H I :: "'b group"
    assume "group_iso_rel G H" "group_iso_rel H I"
    then obtain \<phi> \<psi> where "\<phi> \<in> Rep_group G \<cong> Rep_group H" "\<psi> \<in> Rep_group H \<cong> Rep_group I" unfolding group_iso_rel_def by auto
    then obtain \<pi> where "\<pi> \<in> Rep_group G \<cong> Rep_group I" using group.iso_trans Rep_group by fastforce
    thus "group_iso_rel G I" unfolding group_iso_rel_def by auto
  qed
qed

text {* This assigns to a given group the group isomorphism class *}

definition (in group) iso_class :: "'a group_iso_class"
  where "iso_class = Abs_group_iso_class (Abs_group (monoid.truncate G)) "

end
