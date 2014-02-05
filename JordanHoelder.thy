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

theorem jordan_hoelder_quotients:
  shows "multiset_of series\<GG>.quotient_list = multiset_of series\<HH>.quotient_list"
sorry

find_theorems "(?H \<inter> ?J) \<lhd> ?G"

text {* As a corollary, we see that the composition series of a fixed group
all have the same length. *}

corollary jordan_hoelder_size:
  shows "length \<GG> = length \<HH>"
proof -
  have "length \<GG> = length series\<GG>.quotient_list + 1" by (rule series\<GG>.quotient_list_length[symmetric])
  also have "length series\<GG>.quotient_list + 1 = length series\<HH>.quotient_list + 1" using jordan_hoelder_quotients multiset_of_eq_length by auto
  also have "length series\<HH>.quotient_list + 1 = length \<HH>" by (rule series\<HH>.quotient_list_length)
  finally show ?thesis .
qed

end

end
