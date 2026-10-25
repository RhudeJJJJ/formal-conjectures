/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode168
import Proofs.RadenkovicGutmanD14Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e169 : NestedArithmetic.Expr 3 := .times e168 e122
noncomputable def p169 : NestedHorner.Poly 3 := [[[1]],[[0,0]],[[15,0]],[[0,0]],[[94,0]],[[0,0]],[[319,0]],[[0,0]],[[636,0]],[[0,0]],[[757,1]],[[0,0]],[[522,7]],[[0,0]],[[189,16]],[[0,0]],[[27,13]],[[0,0]],[[0,3]]]
theorem step169 : p169=NestedArithmetic.mul p168 p122 := by decide +kernel
#print axioms step169
theorem h169 : NestedArithmetic.compile e169=p169 := StagedExprCompile.compile_times e169 e168 e122 p168 p122 p169 rfl h168 h122 step169
#print axioms h169
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
