/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode164
import Proofs.RadenkovicGutmanD29Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-54],[0]],[[0,0],[0]],[[-802,0],[0,0]],[[0,0],[0,0]],[[-4964,0],[0,0]],[[0,0],[0,0]],[[-16578,0],[0,0]],[[0,0],[0,0]],[[-32344,0],[0,0]],[[0,0],[0,0]],[[-37272,-54],[-54,0]],[[0,0],[0,0]],[[-24092,-432],[-432,0]],[[0,0],[0,0]],[[-6898,-1188],[-1188,0]],[[0,0],[0,0]],[[462,-1296],[-1296,0]],[[0,0],[0,0]],[[558,-486],[-486,0]],[[0],[0,0]],[[0],[0,-54]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
