/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode044
import Proofs.RadenkovicGutmanD14Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,14]],[[0,0],[0,0]],[[-126,126],[126,2]],[[0,0],[0]],[[24,354],[354]],[[0,0],[0]],[[2344,356],[356]],[[0,0],[0]],[[7530,156],[156]],[[0,0],[0]],[[11612,30],[30]],[[0,0],[0]],[[10416,2],[2]],[[0]],[[5738]],[[0]],[[1954]],[[0]],[[398]],[[0]],[[44]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
