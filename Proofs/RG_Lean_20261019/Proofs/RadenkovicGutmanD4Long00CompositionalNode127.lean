/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode006
import Proofs.RadenkovicGutmanD4Long00CompositionalNode001
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e127 : NestedArithmetic.Expr 3 := .times e006 e001
noncomputable def p127 : NestedHorner.Poly 3 := [[[]],[[0]],[[0]],[[0]],[[1]]]
theorem step127 : p127=NestedArithmetic.mul p006 p001 := by decide +kernel
#print axioms step127
theorem h127 : NestedArithmetic.compile e127=p127 := StagedExprCompile.compile_times e127 e006 e001 p006 p001 p127 rfl h006 h001 step127
#print axioms h127
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
