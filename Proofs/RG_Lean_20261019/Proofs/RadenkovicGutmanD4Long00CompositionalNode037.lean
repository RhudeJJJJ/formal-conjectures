/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode036
import Proofs.RadenkovicGutmanD4Long00CompositionalNode031
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e037 : NestedArithmetic.Expr 3 := .times e036 e031
noncomputable def p037 : NestedHorner.Poly 3 := [[[0],[0,-2]],[[0,0],[0]],[[18,-18],[-18]],[[0,0],[0]],[[-6,-48],[-48]],[[0,0],[0]],[[-334,-44],[-44]],[[0,0],[0]],[[-1028,-16],[-16]],[[0,0],[0]],[[-1512,-2],[-2]],[[0]],[[-1272]],[[0]],[[-638]],[[0]],[[-188]],[[0]],[[-30]],[[0]],[[-2]]]
theorem step037 : p037=NestedArithmetic.mul p036 p031 := by decide +kernel
#print axioms step037
theorem h037 : NestedArithmetic.compile e037=p037 := StagedExprCompile.compile_times e037 e036 e031 p036 p031 p037 rfl h036 h031 step037
#print axioms h037
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
