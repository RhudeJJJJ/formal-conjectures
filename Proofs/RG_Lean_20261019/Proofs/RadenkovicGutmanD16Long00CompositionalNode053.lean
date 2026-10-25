/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode030
import Proofs.RadenkovicGutmanD16Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,16]],[[0,0],[0]],[[144,144],[144]],[[0,0],[0]],[[2544,384],[384]],[[0,0],[0]],[[11152,352],[352]],[[0,0],[0]],[[22880,128],[128]],[[0,0],[0]],[[26304,16],[16]],[[0]],[[18176]],[[0]],[[7696]],[[0]],[[1952]],[[0]],[[272]],[[0]],[[16]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
