/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode044
import Proofs.RadenkovicGutmanD27Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,27]],[[0,0],[0,0]],[[-243,243],[243,2]],[[0,0],[0]],[[63,666],[666]],[[0,0],[0]],[[4515,642],[642]],[[0,0],[0]],[[14212,260],[260]],[[0,0],[0]],[[21440,43],[43]],[[0,0],[0]],[[18684,2],[2]],[[0]],[[9885]],[[0]],[[3176]],[[0]],[[593]],[[0]],[[57]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
