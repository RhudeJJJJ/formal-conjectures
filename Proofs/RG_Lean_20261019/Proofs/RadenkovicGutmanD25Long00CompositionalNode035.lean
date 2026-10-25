/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode034
import Proofs.RadenkovicGutmanD25Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-75],[-75]],[[0,0],[0]],[[-1350,-325],[-325]],[[0,0],[0]],[[-9450,-400],[-400]],[[0,0],[0]],[[-26100,-175],[-175]],[[0,0],[0]],[[-37850,-25],[-25]],[[0]],[[-31800]],[[0]],[[-15950]],[[0]],[[-4700]],[[0]],[[-750]],[[0]],[[-50]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
