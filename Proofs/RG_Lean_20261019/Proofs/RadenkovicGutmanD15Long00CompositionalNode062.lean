/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode044
import Proofs.RadenkovicGutmanD15Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,15]],[[0,0],[0,0]],[[135,135],[135,2]],[[0,0],[0]],[[2403,378],[378]],[[0,0],[0]],[[10773,378],[378]],[[0,0],[0]],[[22844,164],[164]],[[0,0],[0]],[[27520,31],[31]],[[0,0],[0]],[[20328,2],[2]],[[0]],[[9487]],[[0]],[[2792]],[[0]],[[499]],[[0]],[[49]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
