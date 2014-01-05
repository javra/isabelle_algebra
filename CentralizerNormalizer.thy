(*  Title:      CentralizerNormalizer.thy
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
*)

theory CentralizerNormalizer
imports
  "~~/src/HOL/Algebra/Group"
  "~~/src/HOL/Algebra/Coset"
  "SubgroupConjugation"
  "GroupAction"
begin

context group
begin

definition centralizer
  where "centralizer S = {g\<in>carrier G. \<forall>s\<in>S. s \<otimes> g = g \<otimes> s}"

definition normalizer
  where "normalizer S = {g\<in>carrier G. g <# S = S #> g}"


end

end
