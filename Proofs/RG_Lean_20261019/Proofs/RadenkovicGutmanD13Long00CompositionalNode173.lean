/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode165
import Proofs.RadenkovicGutmanD13Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-22],[0]],[[0,0],[0]],[[-296,0],[0,0]],[[0,0],[0,0]],[[-1566,0],[0,0]],[[0,0],[0,0]],[[-3926,0],[0,0]],[[0,0],[0,0]],[[-3698,0],[0,0]],[[0,0],[0,0]],[[3456,-22],[-22,0]],[[0,0],[0,0]],[[12038,-163],[-163,0]],[[0,0],[0,0]],[[12018,-393],[-393,0]],[[0,0],[0,0]],[[5472,-320],[-320,0]],[[0,0],[0,0]],[[972,-29],[-29,0]],[[0,0],[0,0]],[[0,39],[39,-22]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
