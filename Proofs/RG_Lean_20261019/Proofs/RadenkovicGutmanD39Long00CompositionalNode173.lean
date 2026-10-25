/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode165
import Proofs.RadenkovicGutmanD39Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-74],[0]],[[0,0],[0]],[[-1024,0],[0,0]],[[0,0],[0,0]],[[-5674,0],[0,0]],[[0,0],[0,0]],[[-15626,0],[0,0]],[[0,0],[0,0]],[[-20182,0],[0,0]],[[0,0],[0,0]],[[-2784,-74],[-74,0]],[[0,0],[0,0]],[[24674,-553],[-553,0]],[[0,0],[0,0]],[[30478,-1355],[-1355,0]],[[0,0],[0,0]],[[15144,-1152],[-1152,0]],[[0,0],[0,0]],[[2844,-159],[-159,0]],[[0,0],[0,0]],[[0,117],[117,-74]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
