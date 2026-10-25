/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode034
import Proofs.RadenkovicGutmanD37Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-111],[-111]],[[0,0],[0]],[[-1998,-481],[-481]],[[0,0],[0]],[[-13986,-592],[-592]],[[0,0],[0]],[[-38628,-259],[-259]],[[0,0],[0]],[[-56018,-37],[-37]],[[0]],[[-47064]],[[0]],[[-23606]],[[0]],[[-6956]],[[0]],[[-1110]],[[0]],[[-74]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
