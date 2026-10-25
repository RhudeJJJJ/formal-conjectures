/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode030
import Proofs.RadenkovicGutmanD32Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,32]],[[0,0],[0]],[[288,288],[288]],[[0,0],[0]],[[5088,768],[768]],[[0,0],[0]],[[22304,704],[704]],[[0,0],[0]],[[45760,256],[256]],[[0,0],[0]],[[52608,32],[32]],[[0]],[[36352]],[[0]],[[15392]],[[0]],[[3904]],[[0]],[[544]],[[0]],[[32]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
