/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode043
import Proofs.RadenkovicGutmanD12Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,1296],[0,2592,-1440],[1296,-1440,400]],[[0,0,0],[0,0,0],[0,0]],[[0,45360,-1728],[45360,-28656,960],[-1728,960]],[[0,0,0],[0,0,0],[0,0]],[[324000,168480,-20160],[168480,-150720,11520],[-20160,11520]],[[0,0,0],[0,0,0],[0,0]],[[2214000,-253584,-11808],[-253584,-157936,14240],[-11808,14240]],[[0,0,0],[0,0,0],[0,0]],[[2080080,-2357040,89376],[-2357040,266272,5920],[89376,5920]],[[0,0,0],[0,0,0],[0,0]],[[-28846320,-4673712,210720],[-4673712,806400,800],[210720,800]],[[0,0,0],[0,0],[0]],[[-147626336,-2271424,212944],[-2271424,848448],[212944]],[[0,0,0],[0,0],[0]],[[-365983328,6078752,116896],[6078752,470032],[116896]],[[0,0,0],[0,0],[0]],[[-562590080,13602352,36144],[13602352,145408],[36144]],[[0,0,0],[0,0],[0]],[[-560620400,13925936,5920],[13925936,23760],[5920]],[[0,0,0],[0,0],[0]],[[-335422496,8782768,400],[8782768,1600],[400]],[[0,0],[0]],[[-58161280,3644880],[3644880]],[[0,0],[0]],[[98160544,1001024],[1001024]],[[0,0],[0]],[[112673840,175568],[175568]],[[0,0],[0]],[[66322144,17840],[17840]],[[0,0],[0]],[[25782240,800],[800]],[[0]],[[6961920]],[[0]],[[1300528]],[[0]],[[161024]],[[0]],[[11920]],[[0]],[[400]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
