/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode180
import Proofs.RadenkovicGutmanD4Long00CompositionalNode121
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e181 : NestedArithmetic.Expr 3 := .times e180 e121
noncomputable def p181 : NestedHorner.Poly 3 := [[[-1]],[[0]],[[-14]],[[0]],[[-81]],[[0]],[[-250]],[[0]],[[-444]],[[0]],[[-458]],[[0]],[[-265]],[[0]],[[-78]],[[0]],[[-9]]]
theorem step181 : p181=NestedArithmetic.mul p180 p121 := by decide +kernel
#print axioms step181
theorem h181 : NestedArithmetic.compile e181=p181 := StagedExprCompile.compile_times e181 e180 e121 p180 p121 p181 rfl h180 h121 step181
#print axioms h181
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
