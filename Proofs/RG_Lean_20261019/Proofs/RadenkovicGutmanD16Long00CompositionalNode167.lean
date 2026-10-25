/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode166
import Proofs.RadenkovicGutmanD16Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e167 : NestedArithmetic.Expr 3 := .times e166 e122
noncomputable def p167 : NestedHorner.Poly 3 := [[[1],[]],[[0],[0]],[[15],[0]],[[0],[0]],[[94],[0]],[[0],[0]],[[319],[0]],[[0],[0]],[[636],[0]],[[0],[0]],[[757],[1]],[[0],[0]],[[522],[7]],[[0],[0]],[[189],[16]],[[0],[0]],[[27],[13]],[[],[0]],[[],[3]]]
theorem step167 : p167=NestedArithmetic.mul p166 p122 := by decide +kernel
#print axioms step167
theorem h167 : NestedArithmetic.compile e167=p167 := StagedExprCompile.compile_times e167 e166 e122 p166 p122 p167 rfl h166 h122 step167
#print axioms h167
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
