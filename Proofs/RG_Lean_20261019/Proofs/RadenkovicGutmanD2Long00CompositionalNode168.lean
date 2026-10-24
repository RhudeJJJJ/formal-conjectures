/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode165
import Proofs.RadenkovicGutmanD2Long00CompositionalNode167
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e168 : NestedArithmetic.Expr 3 := .plus e165 e167
noncomputable def p168 : NestedHorner.Poly 3 := [[[2],[]],[[0,0],[0]],[[30,0],[0]],[[0,0],[0]],[[188,0],[0]],[[0,0],[0]],[[638,0],[0]],[[0,0],[0]],[[1272,0],[0]],[[0,0],[0]],[[1514,1],[1]],[[0,0],[0]],[[1044,7],[7]],[[0,0],[0]],[[378,16],[16]],[[0,0],[0]],[[54,13],[13]],[[0,0],[0]],[[0,3],[3]]]
theorem step168 : p168=NestedHorner.add p165 p167 := by decide +kernel
#print axioms step168
theorem h168 : NestedArithmetic.compile e168=p168 := StagedExprCompile.compile_plus e168 e165 e167 p165 p167 p168 rfl h165 h167 step168
#print axioms h168
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
