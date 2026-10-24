/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode169
import Proofs.RadenkovicGutmanD4Long00CompositionalNode121
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e169 e121
noncomputable def p178 : NestedHorner.Poly 3 := [[[2],[]],[[0,0],[0]],[[30,0],[0]],[[0,0],[0]],[[188,0],[0]],[[0,0],[0]],[[638,0],[0]],[[0,0],[0]],[[1272,0],[0]],[[0,0],[0]],[[1514,1],[1]],[[0,0],[0]],[[1044,7],[7]],[[0,0],[0]],[[378,16],[16]],[[0,0],[0]],[[54,13],[13]],[[0,0],[0]],[[0,3],[3]]]
theorem step178 : p178=NestedArithmetic.mul p169 p121 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e169 e121 p169 p121 p178 rfl h169 h121 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
