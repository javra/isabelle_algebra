(*  Title:      The Jordan Hölder Theorem
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
    Maintainer: Jakob von Raumer <jakob.raumer@student.kit.edu>
*)

theory JordanHoelder
imports
  "CompositionSeries"
begin

locale jordan_hoelder = group
  + series\<HH>: composition_series G \<HH>
  + series\<GG>: composition_series G \<GG>
  for \<HH> and \<GG>

(*context jordan_hoelder
begin*)

theorem jordan_hoelder_quotients:
  shows "group G \<Longrightarrow> composition_series G \<GG> \<Longrightarrow> composition_series G \<HH> \<Longrightarrow> 
        length \<GG> = length \<HH> \<Longrightarrow>((\<And>isoms \<pi>. length isoms + 1 = length \<GG> \<Longrightarrow>
        \<pi> \<in> Bij {0..<length \<GG> - 1} \<Longrightarrow>
        (\<And>i. i + 1 < length \<GG> \<Longrightarrow> isoms ! i \<in> normal_series.quotient_list G \<GG> ! i \<cong> normal_series.quotient_list G \<HH> ! \<pi> i) \<Longrightarrow>
        thesis) \<Longrightarrow> thesis)"
proof (induction "length \<GG>" arbitrary: \<GG> \<HH> G rule: full_nat_induct)
  case 1
  then interpret comp\<GG>: composition_series G \<GG> by simp
  from 1 interpret comp\<HH>: composition_series G \<HH> by simp
  from 1 interpret grpG: group G by simp
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
      ultimately show thesis using 1(6) by auto
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
      ultimately show thesis using 1(6) eq_quotients iso_refl length by fastforce
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
    obtain l where l:"length \<HH> = l + 1" using comp\<HH>.notempty by (metis comp\<HH>.quotient_list_length)
    show thesis
    proof (cases "l \<ge> k")
      case False
      with l k have "Suc (length \<HH>) \<le> length \<GG>" by simp
      then obtain isoms \<pi> where i\<pi>:"length isoms + 1 = length \<HH>" "\<pi> \<in> Bij {0 ..< length \<HH> - 1}" "length \<GG> = length \<HH>"
        "\<And>i. i+1 < length \<HH> \<Longrightarrow> isoms ! i \<in> normal_series.quotient_list G \<HH> ! i \<cong> normal_series.quotient_list G \<GG> ! (\<pi> i)"
      by (metis "1.prems"(4) Suc_n_not_le_n)
      def \<pi>' \<equiv> "(\<lambda>x \<in> {0 ..< length \<GG> - 1}. (inv_into {0 ..< length \<GG> - 1} \<pi>) x)"
      def isoms' \<equiv> "map (\<lambda>i. inv_into (carrier (normal_series.quotient_list G \<HH> ! (\<pi>' i))) (isoms ! (\<pi>' i)) ) [0 ..< length \<GG> - 1]"
      hence "length isoms' + 1 = length \<GG>" by (metis (lifting) Suc_eq_plus1 diff_Suc_1 diff_zero k length_map length_upt)
      moreover have "\<pi>' \<in> Bij {0 ..< length \<GG> - 1}" using i\<pi>(2) i\<pi>(3) unfolding \<pi>'_def by (metis restrict_inv_into_Bij)
      moreover have "\<And>i. i + 1 < length \<GG> \<Longrightarrow> isoms' ! i \<in> normal_series.quotient_list G \<GG> ! i \<cong> normal_series.quotient_list G \<HH> ! \<pi>' i"
      proof -
        fix i
        assume "i + 1 < length \<GG>"
        hence "(\<pi> i) + 1 < length \<GG>" using i\<pi> by auto
        with i\<pi> have "isoms ! i \<in> normal_series.quotient_list G \<HH> ! i \<cong> normal_series.quotient_list G \<GG> ! (\<pi> i)" by simp
        
        show "isoms' ! i \<in> normal_series.quotient_list G \<GG> ! i \<cong> normal_series.quotient_list G \<HH> ! \<pi>' i" sorry
      qed
      ultimately show thesis using 1(6) by auto
    next
      case True
      hence l2:"l \<ge> 2" using l k k2 by simp
      with l k have lsmall:"(l - 1) + 1 < length \<HH>" by auto
      def H' \<equiv> "\<HH> ! (l - 1)"
      hence "H' \<lhd> G\<lparr>carrier := \<HH> ! ((l - 1) + 1)\<rparr>" using lsmall comp\<HH>.normal by auto
      hence H'G:"H' \<lhd> G" unfolding H'_def using l l2 comp\<HH>.last last_conv_nth comp\<HH>.notempty by fastforce
      def N \<equiv> "G' \<inter> H'"
      with H'G G'G have NG:"N \<lhd> G" by (metis comp\<GG>.normal_subgroup_intersect)
      show thesis
      proof (cases "N = {\<one>\<^bsub>G\<^esub>}")
        case True
        
      next
        case False
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
