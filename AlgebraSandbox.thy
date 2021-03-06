(*  Title:      AlgebraSandbox.thy
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
*)

theory AlgebraSandbox
imports
  "~~/src/HOL/Algebra/Ideal"
  "~~/src/HOL/Algebra/Group"
  "~~/src/HOL/Algebra/IntRing"
  "~~/src/HOL/Algebra/Bij"
  "~~/src/HOL/Algebra/Sylow"
  "~~/src/HOL/Algebra/Coset"
  "~~/src/HOL/Hilbert_Choice"
  "SndSylow"
begin

(*Zero is contained in every ideal*)
lemma (in ideal) zero_in_ideal:
  shows "\<zero> \<in> I"
by (metis additive_subgroup.zero_closed is_additive_subgroup)

(*An Ideal is an additive subgroup*)
lemma (in ideal) ideal_additive_subgroup:
  shows "additive_subgroup I R"
by (rule local.is_additive_subgroup)

(*The preimage of an ideal is an ideal*)
lemma (in ring_hom_cring) ideal_preimage:
  assumes idealJ:"ideal J S"
  shows "ideal {r \<in> carrier R. h r \<in> J} R"
apply(rule idealI)
  apply (rule R.is_ring)
  apply (rule group.subgroupI)
  apply (rule R.add.is_group)
  apply auto
proof -
  have "\<zero> \<in> carrier R" by (rule R.zero_closed)
  moreover have "h \<zero> = \<zero>\<^bsub>S\<^esub>" by (rule hom_zero)
  with idealJ have "h \<zero> \<in> J" by (metis ideal.zero_in_ideal)
  ultimately show "\<exists>x. x \<in> carrier R \<and> h x \<in> J" by auto
next
  fix a
  assume a:"a \<in> carrier R"
  assume haJ:"h a \<in> J"
  have "h (inv\<^bsub>\<lparr>carrier = carrier R, mult = op \<oplus>, one = \<zero>\<rparr>\<^esub> a)
    = inv\<^bsub>\<lparr>carrier = carrier S, mult = op \<oplus>\<^bsub>S\<^esub>, one = \<zero>\<^bsub>S\<^esub>\<rparr>\<^esub>(h a)" by (metis a a_inv_def hom_a_inv)
  moreover from idealJ have "additive_subgroup J S" by (rule ideal.ideal_additive_subgroup)
  with haJ have "inv\<^bsub>\<lparr>carrier = carrier S, mult = op \<oplus>\<^bsub>S\<^esub>, one = \<zero>\<^bsub>S\<^esub>\<rparr>\<^esub> (h a) \<in> J"
    by (metis a_inv_def additive_subgroup.a_inv_closed additive_subgroupI)
  ultimately show "h (inv\<^bsub>\<lparr>carrier = carrier R, mult = op \<oplus>, one = \<zero>\<rparr>\<^esub> a) \<in> J" by simp
next
  fix a b
  assume assm:"h a \<in> J" "h b \<in> J"
  thus "h a \<oplus>\<^bsub>S\<^esub> h b \<in> J" 
    by (metis additive_subgroup.a_closed ideal.ideal_additive_subgroup idealJ)
next
  fix a x
  assume "h a \<in> J" "x \<in> carrier R"
  thus "h x \<otimes>\<^bsub>S\<^esub> h a \<in> J" by (metis hom_closed ideal.I_l_closed idealJ)
next
  fix a x
  assume "h a \<in> J" "x \<in> carrier R"
  thus "h a \<otimes>\<^bsub>S\<^esub> h x \<in> J" by (metis hom_closed ideal.I_r_closed idealJ)
qed

subsection {*The actual exercise*}

(*The preimage of a primeideal is a primeideal*)
lemma (in ring_hom_cring) primeideal_preimage:
  assumes primeJ:"primeideal J S"
  shows "primeideal {r \<in> carrier R. h r \<in> J} R"
proof(rule primeidealI)
  from primeJ have "ideal J S" unfolding primeideal_def..
  thus "ideal {r \<in> carrier R. h r \<in> J} R" by (rule ideal_preimage) 
next
  show "cring R" by (rule R.is_cring)
next
  show "carrier R \<noteq> {r \<in> carrier R. h r \<in> J}"
  proof(rule ccontr)
    assume "\<not> carrier R \<noteq> {r \<in> carrier R. h r \<in> J}"
    hence "carrier R = {r \<in> carrier R. h r \<in> J}" by simp
    hence "\<one> \<in> {r \<in> carrier R. h r \<in> J}" by (simp add:R.one_closed)
    hence "h \<one> \<in> J" by simp
    hence "J = carrier S" by (metis primeideal_def hom_one ideal.one_imp_carrier primeJ)
    thus "False" by (metis primeJ primeideal.I_notcarr)
  qed
next
  fix a b
  assume a:"a \<in> carrier R"
  assume b:"b \<in> carrier R" 
  assume ab:"a \<otimes> b \<in> {r \<in> carrier R. h r \<in> J}"
  hence "h (a \<otimes> b) \<in> J" by simp
  hence "(h a) \<otimes>\<^bsub>S\<^esub> (h b) \<in> J" by (metis a b hom_mult)
  hence "h a \<in> J \<or> h b \<in> J" by (metis a assms b hom_closed primeideal.I_prime)
  thus "a \<in> {r \<in> carrier R. h r \<in> J} \<or> b \<in> {r \<in> carrier R. h r \<in> J}" by (metis a b mem_Collect_eq)
qed

section {*Aufgabe 2b*}

(*The definition of the direct product of two rings*)

definition ringProd :: "_ \<Rightarrow> _ \<Rightarrow> ('a \<times> 'b) ring"
  where "ringProd R S = \<lparr> carrier = carrier R \<times> carrier S,
    mult = (\<lambda>(r,s) (r',s'). (r \<otimes>\<^bsub>R\<^esub> r', s \<otimes>\<^bsub>S\<^esub> s')),
    one = (\<one>\<^bsub>R\<^esub>, \<one>\<^bsub>S\<^esub>),
    zero = (\<zero>\<^bsub>R\<^esub>, \<zero>\<^bsub>S\<^esub>),
    add = (\<lambda>(r,s) (r',s'). (r \<oplus>\<^bsub>R\<^esub> r', s \<oplus>\<^bsub>S\<^esub> s')) \<rparr>"


(* The direct product of two abelian groups is an abelian group *)

lemma dirProd_preserves_comm:
  assumes "comm_group G" "comm_group H"
  shows "comm_group (G \<times>\<times> H)"
proof (rule group.group_comm_groupI)
  from assms have "group G" "group H" unfolding comm_group_def by simp_all
  thus "group (G \<times>\<times> H)" by (rule DirProd_group)
next
  fix x y
  assume a:"x \<in> carrier (G \<times>\<times> H)" "y \<in> carrier (G \<times>\<times> H)"
  hence "x \<otimes>\<^bsub>G \<times>\<times> H\<^esub> y = ((fst x) \<otimes>\<^bsub>G\<^esub> (fst y), (snd x) \<otimes>\<^bsub>H\<^esub> (snd y))" 
  unfolding DirProd_def by auto
  also  have "... = ((fst y) \<otimes>\<^bsub>G\<^esub> (fst x), (snd y) \<otimes>\<^bsub>H\<^esub> (snd x))"
  proof(rule prod_eqI)
    from a have "fst x \<in> carrier G" "fst y \<in> carrier G" by auto
    with `comm_group G` have "(fst x) \<otimes>\<^bsub>G\<^esub> (fst y) = (fst y) \<otimes>\<^bsub>G\<^esub> (fst x)"
      unfolding comm_group_def by (metis comm_monoid.m_comm)
    thus "fst (fst x \<otimes>\<^bsub>G\<^esub> fst y, snd x \<otimes>\<^bsub>H\<^esub> snd y) =
    fst (fst y \<otimes>\<^bsub>G\<^esub> fst x, snd y \<otimes>\<^bsub>H\<^esub> snd x)" by simp
  next
    from a have "snd x \<in> carrier H" "snd y \<in> carrier H" by auto
    with `comm_group H` have "(snd x) \<otimes>\<^bsub>H\<^esub> (snd y) = (snd y) \<otimes>\<^bsub>H\<^esub> (snd x)"
      unfolding comm_group_def by (metis comm_monoid.m_comm)
    thus "snd (fst x \<otimes>\<^bsub>G\<^esub> fst y, snd x \<otimes>\<^bsub>H\<^esub> snd y) =
    snd (fst y \<otimes>\<^bsub>G\<^esub> fst x, snd y \<otimes>\<^bsub>H\<^esub> snd x)" by simp
  qed
  also with a have "... = y \<otimes>\<^bsub>G \<times>\<times> H\<^esub> x" unfolding DirProd_def by auto
  ultimately show "x \<otimes>\<^bsub>G \<times>\<times> H\<^esub> y = y \<otimes>\<^bsub>G \<times>\<times> H\<^esub> x" by simp
qed  

lemma ringProd_ring:
  assumes "ring R" "ring S"
  shows "ring (RingProd R S)"

sorry

(* The components of map between two rings make up a ring homomorphism if they are themselves
  ring homomorphisms. *)

lemma ring_prod_hom_from_hom:
  assumes fst:"(fst \<circ> h) \<in> ring_hom R S"
  assumes snd:" (snd \<circ> h) \<in> ring_hom R S'"
  shows "h \<in> ring_hom R (ringProd S S')"
unfolding ring_hom_def
apply(simp)
apply(rule conjI)
apply(rule funcsetI)
unfolding ringProd_def
apply(auto)
proof -
  fix x
  assume "x \<in> carrier R"
  with fst snd have "fst (h x) \<in> carrier S"  "snd (h x) \<in> carrier S'"
    by (metis o_eq_dest_lhs ring_hom_closed)+
  hence "h x \<in> {(s,s'). s \<in> carrier S \<and> s' \<in> carrier S'}" by (metis (lifting) mem_Collect_eq prod_case_unfold)
  thus "h x \<in> carrier S \<times> carrier S'" by (metis Collect_mem_eq Collect_split)
next
  (*Note: This should actually proven via the ring homomorphism "product" being the "product"
    of monoid morphisms. *)
  fix x y
  assume a:"x \<in> carrier R" "y \<in> carrier R"
  with fst snd have homImp:"(fst \<circ> h) x \<otimes>\<^bsub>S\<^esub> (fst \<circ> h) y = (fst \<circ> h) (x \<otimes>\<^bsub>R\<^esub> y)"
    "(snd \<circ> h) x \<otimes>\<^bsub>S'\<^esub> (snd \<circ> h) y = (snd \<circ> h) (x \<otimes>\<^bsub>R\<^esub> y)" by (auto dest:ring_hom_mult)
  have "(\<lambda>(r, s) (r', s'). (r \<otimes>\<^bsub>S\<^esub> r', s \<otimes>\<^bsub>S'\<^esub> s')) (h x) (h y)
    = (fst (h x) \<otimes>\<^bsub>S\<^esub> fst (h y), snd (h x) \<otimes>\<^bsub>S'\<^esub> snd (h y))" by (metis (lifting) prod_case_unfold)
  also from homImp have "... = ((fst \<circ> h) (x \<otimes>\<^bsub>R\<^esub> y), (snd \<circ> h) (x \<otimes>\<^bsub>R\<^esub> y))" by simp
  also have "... = h (x \<otimes>\<^bsub>R\<^esub> y)" by (metis comp_apply pair_collapse)
  finally show "h (x \<otimes>\<^bsub>R\<^esub> y) = (\<lambda>(r, s) (r', s'). (r \<otimes>\<^bsub>S\<^esub> r', s \<otimes>\<^bsub>S'\<^esub> s')) (h x) (h y)"..
next
  fix x y
  assume a:"x \<in> carrier R" "y \<in> carrier R"
  with fst snd have homImp:"(fst \<circ> h) x \<oplus>\<^bsub>S\<^esub> (fst \<circ> h) y = (fst \<circ> h) (x \<oplus>\<^bsub>R\<^esub> y)"
    "(snd \<circ> h) x \<oplus>\<^bsub>S'\<^esub> (snd \<circ> h) y = (snd \<circ> h) (x \<oplus>\<^bsub>R\<^esub> y)" by (auto dest:ring_hom_add)
  have "(\<lambda>(r, s) (r', s'). (r \<oplus>\<^bsub>S\<^esub> r', s \<oplus>\<^bsub>S'\<^esub> s')) (h x) (h y)
    = (fst (h x) \<oplus>\<^bsub>S\<^esub> fst (h y), snd (h x) \<oplus>\<^bsub>S'\<^esub> snd (h y))" by (metis (lifting) prod_case_unfold)
  also from homImp have "... = ((fst \<circ> h) (x \<oplus>\<^bsub>R\<^esub> y), (snd \<circ> h) (x \<oplus>\<^bsub>R\<^esub> y))" by simp
  also have "... = h (x \<oplus>\<^bsub>R\<^esub> y)" by (metis comp_apply pair_collapse)
  finally show "h (x \<oplus>\<^bsub>R\<^esub> y) = (\<lambda>(r, s) (r', s'). (r \<oplus>\<^bsub>S\<^esub> r', s \<oplus>\<^bsub>S'\<^esub> s')) (h x) (h y)"..
next
  from fst snd show "h \<one>\<^bsub>R\<^esub> = (\<one>\<^bsub>S\<^esub>, \<one>\<^bsub>S'\<^esub>)" by (metis comp_apply pair_collapse ring_hom_one)
qed

(* Interpret a commutative ring as a (general) ring *)

lemma (in cring) is_ring:
  assumes "cring R"
  shows "ring R"
by (metis is_ring)

(* The direct product of two commutative rings is commutative. *)

lemma cringProd_cring:
  assumes cringR:"cring R"
  assumes cringS:"cring S"
  shows "cring (ringProd R S)"
proof -
  from assms have isRing:"ring (ringProd R S)" by (metis cring.is_ring ringProd_ring)
  have "comm_monoid (ringProd R S)"
  proof (rule monoid.monoid_comm_monoidI)
    from isRing show monoid:"monoid (ringProd R S)" by (rule ring.is_monoid)
  next
    fix x y
    assume xyassms:"x \<in> carrier (ringProd R S)" "y \<in> carrier (ringProd R S)"
    then obtain r s r' s' where rsassms:"(r,s) = x" "(r',s') = y" by (metis surj_pair)
    hence "x \<otimes>\<^bsub>ringProd R S\<^esub> y = (r \<otimes>\<^bsub>R\<^esub> r', s \<otimes>\<^bsub>S\<^esub> s')" unfolding ringProd_def by (metis monoid.select_convs(1) split_conv)
    also from xyassms rsassms have rassms:"r \<in> carrier R" "r' \<in> carrier R" unfolding ringProd_def by auto
    with cringR have "(r \<otimes>\<^bsub>R\<^esub> r', s \<otimes>\<^bsub>S\<^esub> s') = (r' \<otimes>\<^bsub>R\<^esub> r, s \<otimes>\<^bsub>S\<^esub> s')" by (metis cring.cring_simprules(14))
    also from xyassms rsassms have sassms:"s \<in> carrier S" "s' \<in> carrier S" unfolding ringProd_def by auto
    with cringS have "(r' \<otimes>\<^bsub>R\<^esub> r, s \<otimes>\<^bsub>S\<^esub> s') = (r' \<otimes>\<^bsub>R\<^esub> r, s' \<otimes>\<^bsub>S\<^esub> s)" by (metis cring.cring_simprules(14))
    also from rsassms have "(r' \<otimes>\<^bsub>R\<^esub> r, s' \<otimes>\<^bsub>S\<^esub> s) = y \<otimes>\<^bsub>ringProd R S\<^esub> x" unfolding ringProd_def by (metis monoid.select_convs(1) split_conv)
    ultimately show "x \<otimes>\<^bsub>ringProd R S\<^esub> y = y \<otimes>\<^bsub>ringProd R S\<^esub> x" unfolding ringProd_def by simp
  qed
  with isRing show ?thesis unfolding cring_def..  
qed

(*The image of an ideal is not neccessarily an ideal*)

lemma ideal_image:
  obtains I R S h
  where "ideal I (R::(int set) ring)" "h \<in> ring_hom R (S::(int set \<times> int set) ring)" "\<not> ideal (h ` I) S"
proof -
  def Z2 \<equiv> "ZFact 2"
  def Z2Z2 \<equiv> "ringProd Z2 Z2"
  have c:"cring Z2" by (metis Z2_def ZFact_is_cring)
  hence r:"ring Z2" by (metis cring.is_ring)
  hence r2:"ring Z2Z2" by (metis Z2Z2_def ringProd_ring)
  def h \<equiv> "\<lambda>x::(int set).(x,x)"
  have a:"h \<in> ring_hom Z2 Z2Z2"
    unfolding Z2Z2_def
  proof(rule ring_prod_hom_from_hom)
    from h_def have "fst \<circ> h = id" by auto
    thus "fst \<circ> h \<in> ring_hom Z2 Z2" by simp
  next
    from h_def have "snd \<circ> h = id" by auto
    thus "snd \<circ> h \<in> ring_hom Z2 Z2" by simp
  qed
  from r have b:"ideal (carrier Z2) Z2" by (metis ring.oneideal)
  have "\<not> ideal (h ` (carrier Z2)) Z2Z2"
  proof -
    from a have "\<one>\<^bsub>Z2Z2\<^esub> \<in> h ` (carrier Z2)" unfolding h_def Z2Z2_def ringProd_def by (metis (mono_tags) image_eqI monoid.select_convs(2) r ring.ring_simprules(6))
    moreover from c have "(\<one>\<^bsub>Z2\<^esub>, \<zero>\<^bsub>Z2\<^esub>) \<in> carrier Z2Z2" unfolding Z2Z2_def ringProd_def by (metis cring.cring_simprules(2) cring.cring_simprules(6) mem_Sigma_iff partial_object.select_convs(1))
    moreover with r2 have Z2Z2simp:"(\<one>\<^bsub>Z2\<^esub>, \<zero>\<^bsub>Z2\<^esub>) \<otimes>\<^bsub>Z2Z2\<^esub> \<one>\<^bsub>Z2Z2\<^esub> = (\<one>\<^bsub>Z2\<^esub>, \<zero>\<^bsub>Z2\<^esub>)" by (metis monoid.r_one ring.is_monoid)
    have "domain Z2" unfolding Z2_def by (metis ZFact_prime_is_domain nat_numeral two_is_prime)
    hence one_not_zero:"\<one>\<^bsub>Z2\<^esub> \<noteq> \<zero>\<^bsub>Z2\<^esub>" by (metis domain.zero_not_one)
    hence "(\<one>\<^bsub>Z2\<^esub>, \<zero>\<^bsub>Z2\<^esub>) \<otimes>\<^bsub>Z2Z2\<^esub> \<one>\<^bsub>Z2Z2\<^esub> \<notin> h ` (carrier Z2)" by (metis Z2Z2simp h_def imageE prod.inject)
    ultimately show ?thesis by (metis r2 a ideal.one_imp_carrier ring.ring_simprules(5) ring_hom_one)
  qed
  with b a show thesis by (rule that)
qed




(*Simple Groups*)

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

(*Symmetric Group*)

definition symmetric_group :: "nat \<Rightarrow> _"
  where "symmetric_group n = BijGroup {1 .. n}"

end
