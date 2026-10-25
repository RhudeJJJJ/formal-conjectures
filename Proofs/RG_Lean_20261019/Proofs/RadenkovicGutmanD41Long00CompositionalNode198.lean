/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode197
import Proofs.RadenkovicGutmanD41Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[235,0],[0,0]],[[0,0],[0,0]],[[3263,0],[0,0]],[[0,0],[0,0]],[[19908,0],[0,0]],[[0,0],[0,0]],[[66667,0],[0,0]],[[0,0],[0,0]],[[131892,2],[2,0]],[[0,0],[0,0]],[[156172,139],[139,0]],[[0,0],[0,0]],[[107016,946],[946,0]],[[0,0],[0,0]],[[37849,2262],[2262,0]],[[0,0],[0,0]],[[4533,2068],[2068,0]],[[0,0],[0,0]],[[-369,615],[615,2]],[[0],[0,0]],[[0],[0,41]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
