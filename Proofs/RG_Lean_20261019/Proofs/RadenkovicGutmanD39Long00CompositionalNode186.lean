/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode178
import Proofs.RadenkovicGutmanD39Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-74],[0]],[[0,0],[0]],[[-1219,0],[0,0]],[[0,0],[0,0]],[[-8404,0],[0,0]],[[0,0],[0,0]],[[-31421,0],[0,0]],[[0,0],[0,0]],[[-68932,0],[0,0]],[[0,0],[0,0]],[[-89364,-74],[-74,0]],[[0,0],[0,0]],[[-64636,-553],[-553,0]],[[0,0],[0,0]],[[-21197,-1355],[-1355,0]],[[0,0],[0,0]],[[-66,-1152],[-1152,0]],[[0,0],[0,0]],[[1089,-159],[-159,0]],[[0,0],[0,0]],[[0,117],[117,-74]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
