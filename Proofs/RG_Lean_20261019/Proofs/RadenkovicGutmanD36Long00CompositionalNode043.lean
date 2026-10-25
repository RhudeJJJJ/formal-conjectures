/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode041
import Proofs.RadenkovicGutmanD36Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,108],[108,-68]],[[0,0],[0]],[[2628,-144],[-144]],[[0,0],[0]],[[14028,-1056],[-1056]],[[0,0],[0]],[[28348,-1244],[-1244]],[[0,0],[0]],[[23216,-508],[-508]],[[0,0],[0]],[[-2064,-68],[-68]],[[0]],[[-18280]],[[0]],[[-14276]],[[0]],[[-5200]],[[0]],[[-940]],[[0]],[[-68]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
