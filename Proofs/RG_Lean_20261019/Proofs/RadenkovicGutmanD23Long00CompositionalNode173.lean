/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode165
import Proofs.RadenkovicGutmanD23Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-42],[0]],[[0,0],[0]],[[-576,0],[0,0]],[[0,0],[0,0]],[[-3146,0],[0,0]],[[0,0],[0,0]],[[-8426,0],[0,0]],[[0,0],[0,0]],[[-10038,0],[0,0]],[[0,0],[0,0]],[[1056,-42],[-42,0]],[[0,0],[0,0]],[[16898,-313],[-313,0]],[[0,0],[0,0]],[[19118,-763],[-763,0]],[[0,0],[0,0]],[[9192,-640],[-640,0]],[[0,0],[0,0]],[[1692,-79],[-79,0]],[[0,0],[0,0]],[[0,69],[69,-42]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
