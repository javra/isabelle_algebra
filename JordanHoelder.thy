(*  Title:      The Jordan Hölder Theorem
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
    Maintainer: Jakob von Raumer <jakob.raumer@student.kit.edu>
*)

theory JordanHoelder
imports
  "Multiset"
  "CompositionSeries"
begin

locale jordan_hoelder = group
  + series\<HH>: composition_series G \<HH>
  + series\<GG>: composition_series G \<GG>
  for \<HH> and \<GG>

context jordan_hoelder
begin

find_theorems name:iso "group ?G"

theorem jordan_hoelder_quotients:
  obtains \<phi>s \<pi>
  where "length \<phi>s + 1 = length \<GG>"
    and "\<pi> \<in> Bij {0 ..< length \<GG> - 1}"
    and "\<And>i. i+1 < length \<GG> \<Longrightarrow> isoms ! i \<in> series\<GG>.quotient_list ! i \<cong> series\<HH>.quotient_list ! (\<pi> i)"
proof(cases "length \<GG> > 3")
  case False
  hence "length \<GG> = 0 \<or> length \<GG> = 1 \<or> length \<GG> = 2 \<or> length \<GG> = 3" by arith
  thus thesis using notempty
  proof auto
    -- {* First trivial case: The series has length 1. *}
    assume length:"length \<GG> = Suc 0"
    hence "length [] + 1 = length \<GG>" by auto
    moreover from length have empty:"{0 ..< length \<GG> - 1} = {}" by auto
    then obtain \<pi> where "\<pi> \<in> (extensional {0 ..< length \<GG> - 1}::((nat \<Rightarrow> nat) set))" by (metis restrict_extensional)
    with empty have "\<pi> \<in> Bij {0 ..< length \<GG> - 1}" unfolding Bij_def bij_betw_def inj_on_def by force
    ultimately show thesis using that empty by auto
  next
    -- {* Second trivial case: The series has length 2. *}
    assume length:"length \<GG> = 2"
    hence "\<GG> = [{\<one>}, carrier G]" by (metis series\<GG>.length_two_unique)
    with length have "series\<GG>.quotient_list = [G Mod {\<one>}]" unfolding quotient_list_def by auto
    
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
