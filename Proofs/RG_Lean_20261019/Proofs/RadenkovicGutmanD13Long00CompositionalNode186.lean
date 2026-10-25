/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode178
import Proofs.RadenkovicGutmanD13Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-22],[0]],[[0,0],[0]],[[-361,0],[0,0]],[[0,0],[0,0]],[[-2476,0],[0,0]],[[0,0],[0,0]],[[-9191,0],[0,0]],[[0,0],[0,0]],[[-19948,0],[0,0]],[[0,0],[0,0]],[[-25404,-22],[-22,0]],[[0,0],[0,0]],[[-17732,-163],[-163,0]],[[0,0],[0,0]],[[-5207,-393],[-393,0]],[[0,0],[0,0]],[[402,-320],[-320,0]],[[0,0],[0,0]],[[387,-29],[-29,0]],[[0,0],[0,0]],[[0,39],[39,-22]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
