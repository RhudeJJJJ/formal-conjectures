/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode030
import Proofs.RadenkovicGutmanD22Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,22]],[[0,0],[0]],[[198,198],[198]],[[0,0],[0]],[[3498,528],[528]],[[0,0],[0]],[[15334,484],[484]],[[0,0],[0]],[[31460,176],[176]],[[0,0],[0]],[[36168,22],[22]],[[0]],[[24992]],[[0]],[[10582]],[[0]],[[2684]],[[0]],[[374]],[[0]],[[22]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
