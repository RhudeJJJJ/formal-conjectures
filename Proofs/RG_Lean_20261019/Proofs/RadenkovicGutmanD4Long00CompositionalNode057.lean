/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode035
import Proofs.RadenkovicGutmanD4Long00CompositionalNode036
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e035 e036
noncomputable def p057 : NestedHorner.Poly 3 := [[[]],[[-4]]]
theorem step057 : p057=NestedArithmetic.mul p035 p036 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e035 e036 p035 p036 p057 rfl h035 h036 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
