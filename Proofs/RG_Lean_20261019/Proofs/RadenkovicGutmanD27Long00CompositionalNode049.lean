/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode045
import Proofs.RadenkovicGutmanD27Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,27]],[[0,0],[0,0]],[[-243,405],[405,2]],[[0,0],[0]],[[2979,1368],[1368]],[[0,0],[0]],[[24927,1506],[1506]],[[0,0],[0]],[[70588,638],[638]],[[0,0],[0]],[[103196,97],[97]],[[0,0],[0]],[[87372,2],[2]],[[0]],[[44337]],[[0]],[[13328]],[[0]],[[2213]],[[0]],[[165]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
