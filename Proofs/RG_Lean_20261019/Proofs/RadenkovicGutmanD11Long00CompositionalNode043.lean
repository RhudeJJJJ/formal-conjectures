/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode041
import Proofs.RadenkovicGutmanD11Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,33],[33,-18]],[[0,0],[0]],[[828,-19],[-19]],[[0,0],[0]],[[4728,-256],[-256]],[[0,0],[0]],[[10598,-319],[-319]],[[0,0],[0]],[[11066,-133],[-133]],[[0,0],[0]],[[3936,-18],[-18]],[[0]],[[-2430]],[[0]],[[-3026]],[[0]],[[-1250]],[[0]],[[-240]],[[0]],[[-18]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
