/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode164
import Proofs.RadenkovicGutmanD36Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-68],[0]],[[0,0],[0]],[[-1012,0],[0,0]],[[0,0],[0,0]],[[-6280,0],[0,0]],[[0,0],[0,0]],[[-21044,0],[0,0]],[[0,0],[0,0]],[[-41248,0],[0,0]],[[0,0],[0,0]],[[-47856,-68],[-68,0]],[[0,0],[0,0]],[[-31288,-544],[-544,0]],[[0,0],[0,0]],[[-9236,-1496],[-1496,0]],[[0,0],[0,0]],[[420,-1632],[-1632,0]],[[0,0],[0,0]],[[684,-612],[-612,0]],[[0],[0,0]],[[0],[0,-68]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
