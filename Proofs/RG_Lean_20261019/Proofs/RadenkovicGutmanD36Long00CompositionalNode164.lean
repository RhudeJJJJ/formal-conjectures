/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode119
import Proofs.RadenkovicGutmanD36Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-68],[0]],[[0,0],[0]],[[-1012,0],[0,0]],[[0,0],[0,0]],[[-6280,0],[0,0]],[[0,0],[0,0]],[[-21044,0],[0,0]],[[0,0],[0,0]],[[-41248,0],[0,0]],[[0,0],[0,0]],[[-47856,-68],[-68,0]],[[0,0],[0,0]],[[-31288,-544],[-544,0]],[[0,0],[0,0]],[[-9236,-1496],[-1496,0]],[[0,0],[0,0]],[[420,-1632],[-1632,0]],[[0,0],[0,0]],[[684,-612],[-612,0]],[[0],[0,0]],[[0],[0,-68]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
