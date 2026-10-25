/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode202
import Proofs.RadenkovicGutmanD15Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[49,0],[0,0]],[[0,0],[0,0]],[[499,0],[0,0]],[[0,0],[0,0]],[[2792,0],[0,0]],[[0,0],[0,0]],[[9487,0],[0,0]],[[0,0],[0,0]],[[20328,2],[2,0]],[[0,0],[0,0]],[[27520,31],[31,0]],[[0,0],[0,0]],[[22844,164],[164,0]],[[0,0],[0,0]],[[10773,378],[378,0]],[[0,0],[0,0]],[[2403,378],[378,0]],[[0,0],[0,0]],[[135,135],[135,2]],[[0],[0,0]],[[0],[0,15]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
