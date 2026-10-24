/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode144
import Proofs.RadenkovicGutmanD4Long00CompositionalNode148
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e149 : NestedArithmetic.Expr 3 := .plus e144 e148
noncomputable def p149 : NestedHorner.Poly 3 := [[[1]],[[0,0]],[[8,0]],[[0,0]],[[22,0]],[[0,0]],[[24,0]],[[0,0]],[[9,0]],[[0,0]],[[0,1]]]
theorem step149 : p149=NestedHorner.add p144 p148 := by decide +kernel
#print axioms step149
theorem h149 : NestedArithmetic.compile e149=p149 := StagedExprCompile.compile_plus e149 e144 e148 p144 p148 p149 rfl h144 h148 step149
#print axioms h149
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
