/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode089
import Proofs.RadenkovicGutmanD18Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1944],[0,1944,-576]],[[0,0,0],[0,0,0],[0,0]],[[0,0,23328],[0,78732,-1836],[23328,-1836]],[[0,0,0],[0,0,0],[0,0]],[[72900,639576,127332],[639576,382968,-16812],[127332,-16812]],[[0,0,0],[0,0,0],[0,0]],[[5453892,5620104,267948],[5620104,642492,-20232],[267948,-20232]],[[0,0,0],[0,0,0],[0,0]],[[59591376,21549564,246240],[21549564,243000,-8316],[246240,-8316]],[[0,0,0],[0,0,0],[0,0]],[[313275708,47165688,35892],[47165688,-575712,-1116],[35892,-1116]],[[0,0,0],[0,0],[0]],[[1004720796,64570716,-118728],[64570716,-879912],[-118728]],[[0,0,0],[0,0],[0]],[[2174099328,56478600,-105516],[56478600,-553284],[-105516]],[[0,0,0],[0,0],[0]],[[3344112432,29949408,-40032],[29949408,-182808],[-40032]],[[0,0,0],[0,0],[0]],[[3759803028,6943788,-7380],[6943788,-31140],[-7380]],[[0,0,0],[0,0],[0]],[[3126948192,-2136888,-540],[-2136888,-2160],[-540]],[[0,0],[0]],[[1918574928,-2374668],[-2374668]],[[0,0],[0]],[[848393064,-908316],[-908316]],[[0,0],[0]],[[251888292,-189972],[-189972]],[[0,0],[0]],[[37901052,-21564],[-21564]],[[0,0],[0]],[[-4518000,-1044],[-1044]],[[0]],[[-4120848]],[[0]],[[-1111284]],[[0]],[[-166428]],[[0]],[[-13860]],[[0]],[[-504]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
