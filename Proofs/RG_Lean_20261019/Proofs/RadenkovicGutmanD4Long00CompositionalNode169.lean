/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode166
import Proofs.RadenkovicGutmanD4Long00CompositionalNode168
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e169 : NestedArithmetic.Expr 3 := .plus e166 e168
noncomputable def p169 : NestedHorner.Poly 3 := [[[2],[]],[[0,0],[0]],[[30,0],[0]],[[0,0],[0]],[[188,0],[0]],[[0,0],[0]],[[638,0],[0]],[[0,0],[0]],[[1272,0],[0]],[[0,0],[0]],[[1514,1],[1]],[[0,0],[0]],[[1044,7],[7]],[[0,0],[0]],[[378,16],[16]],[[0,0],[0]],[[54,13],[13]],[[0,0],[0]],[[0,3],[3]]]
theorem step169 : p169=NestedHorner.add p166 p168 := by decide +kernel
#print axioms step169
theorem h169 : NestedArithmetic.compile e169=p169 := StagedExprCompile.compile_plus e169 e166 e168 p166 p168 p169 rfl h166 h168 step169
#print axioms h169
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
