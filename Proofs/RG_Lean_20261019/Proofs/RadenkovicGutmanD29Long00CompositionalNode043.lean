/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode041
import Proofs.RadenkovicGutmanD29Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,87],[87,-54]],[[0,0],[0]],[[2124,-109],[-109]],[[0,0],[0]],[[11424,-832],[-832]],[[0,0],[0]],[[23378,-985],[-985]],[[0,0],[0]],[[19814,-403],[-403]],[[0,0],[0]],[[-384,-54],[-54]],[[0]],[[-13842]],[[0]],[[-11126]],[[0]],[[-4094]],[[0]],[[-744]],[[0]],[[-54]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
