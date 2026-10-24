/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode044
import Proofs.RadenkovicGutmanD3Long00StagedUNode047
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e048 : NestedArithmetic.Expr 3 := .plus e044 e047
noncomputable def p048 : NestedHorner.Poly 3 := [[[0],[0,3]],[[0,0],[0,0]],[[-27,45],[45,2]],[[0,0],[0]],[[315,168],[168]],[[0,0],[0]],[[2775,210],[210]],[[0,0],[0]],[[8140,110],[110]],[[0,0],[0]],[[12380,25],[25]],[[0,0],[0]],[[11052,2],[2]],[[0]],[[6057]],[[0]],[[2048]],[[0]],[[413]],[[0]],[[45]],[[0]],[[2]]]
theorem step048 : p048=NestedHorner.add p044 p047 := by decide +kernel
#print axioms step048
theorem h048 : NestedArithmetic.compile e048=p048 := StagedExprCompile.compile_plus e048 e044 e047 p044 p047 p048 rfl h044 h047 step048
#print axioms h048
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
