/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode165
import Proofs.RadenkovicGutmanD43Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-82],[0]],[[0,0],[0]],[[-1136,0],[0,0]],[[0,0],[0,0]],[[-6306,0],[0,0]],[[0,0],[0,0]],[[-17426,0],[0,0]],[[0,0],[0,0]],[[-22718,0],[0,0]],[[0,0],[0,0]],[[-3744,-82],[-82,0]],[[0,0],[0,0]],[[26618,-613],[-613,0]],[[0,0],[0,0]],[[33318,-1503],[-1503,0]],[[0,0],[0,0]],[[16632,-1280],[-1280,0]],[[0,0],[0,0]],[[3132,-179],[-179,0]],[[0,0],[0,0]],[[0,129],[129,-82]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
