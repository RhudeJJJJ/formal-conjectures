/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode041
import Proofs.RadenkovicGutmanD39Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,117],[117,-74]],[[0,0],[0]],[[2844,-159],[-159]],[[0,0],[0]],[[15144,-1152],[-1152]],[[0,0],[0]],[[30478,-1355],[-1355]],[[0,0],[0]],[[24674,-553],[-553]],[[0,0],[0]],[[-2784,-74],[-74]],[[0]],[[-20182]],[[0]],[[-15626]],[[0]],[[-5674]],[[0]],[[-1024]],[[0]],[[-74]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
