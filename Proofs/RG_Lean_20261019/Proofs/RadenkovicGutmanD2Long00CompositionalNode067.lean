/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .scaled (-1) e066
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,4]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,120],[0,120,8]],[[0,0,0],[0,0,0],[0,0,0]],[[-324,0,900],[0,3312,592],[900,592,4]],[[0,0,0],[0,0,0],[0,0]],[[-4968,22680,7080],[22680,25824,1096],[7080,1096]],[[0,0,0],[0,0,0],[0,0]],[[110376,241488,23284],[241488,84656,976],[23284,976]],[[0,0,0],[0,0,0],[0,0]],[[1801608,1135944,42096],[1135944,153728,440],[42096,440]],[[0,0,0],[0,0,0],[0,0]],[[11475944,3130608,46424],[3130608,171488,96],[46424,96]],[[0,0,0],[0,0,0],[0,0]],[[43046152,5652328,32768],[5652328,123072,8],[32768,8]],[[0,0,0],[0,0],[0]],[[108558420,7079968,15080],[7079968,57728],[15080]],[[0,0,0],[0,0],[0]],[[196554656,6352312,4496],[6352312,17536],[4496]],[[0,0,0],[0,0],[0]],[[265439208,4153312,836],[4153312,3312],[836]],[[0,0,0],[0,0],[0]],[[273779296,1991848,88],[1991848,352],[88]],[[0,0,0],[0,0],[0]],[[218875920,698512,4],[698512,16],[4]],[[0,0],[0]],[[136777584,176632],[176632]],[[0,0],[0]],[[67031804,31280],[31280]],[[0,0],[0]],[[25724488,3672],[3672]],[[0,0],[0]],[[7679444,256],[256]],[[0,0],[0]],[[1760384,8],[8]],[[0]],[[303220]],[[0]],[[37880]],[[0]],[[3232]],[[0]],[[168]],[[0]],[[4]]]
theorem step067 : p067=NestedHorner.scale (-1) p066 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_scaled (-1) e067 e066 p066 p067 rfl h066 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
