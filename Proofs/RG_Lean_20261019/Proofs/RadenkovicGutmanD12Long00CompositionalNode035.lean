/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode034
import Proofs.RadenkovicGutmanD12Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-36],[-36]],[[0,0],[0]],[[-648,-156],[-156]],[[0,0],[0]],[[-4536,-192],[-192]],[[0,0],[0]],[[-12528,-84],[-84]],[[0,0],[0]],[[-18168,-12],[-12]],[[0]],[[-15264]],[[0]],[[-7656]],[[0]],[[-2256]],[[0]],[[-360]],[[0]],[[-24]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
