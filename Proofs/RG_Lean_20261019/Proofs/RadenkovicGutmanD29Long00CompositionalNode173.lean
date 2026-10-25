/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode165
import Proofs.RadenkovicGutmanD29Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-54],[0]],[[0,0],[0]],[[-744,0],[0,0]],[[0,0],[0,0]],[[-4094,0],[0,0]],[[0,0],[0,0]],[[-11126,0],[0,0]],[[0,0],[0,0]],[[-13842,0],[0,0]],[[0,0],[0,0]],[[-384,-54],[-54,0]],[[0,0],[0,0]],[[19814,-403],[-403,0]],[[0,0],[0,0]],[[23378,-985],[-985,0]],[[0,0],[0,0]],[[11424,-832],[-832,0]],[[0,0],[0,0]],[[2124,-109],[-109,0]],[[0,0],[0,0]],[[0,87],[87,-54]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
