/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode165
import Proofs.RadenkovicGutmanD17Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-30],[0]],[[0,0],[0]],[[-408,0],[0,0]],[[0,0],[0,0]],[[-2198,0],[0,0]],[[0,0],[0,0]],[[-5726,0],[0,0]],[[0,0],[0,0]],[[-6234,0],[0,0]],[[0,0],[0,0]],[[2496,-30],[-30,0]],[[0,0],[0,0]],[[13982,-223],[-223,0]],[[0,0],[0,0]],[[14858,-541],[-541,0]],[[0,0],[0,0]],[[6960,-448],[-448,0]],[[0,0],[0,0]],[[1260,-49],[-49,0]],[[0,0],[0,0]],[[0,51],[51,-30]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
