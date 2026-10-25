/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode034
import Proofs.RadenkovicGutmanD31Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-93],[-93]],[[0,0],[0]],[[-1674,-403],[-403]],[[0,0],[0]],[[-11718,-496],[-496]],[[0,0],[0]],[[-32364,-217],[-217]],[[0,0],[0]],[[-46934,-31],[-31]],[[0]],[[-39432]],[[0]],[[-19778]],[[0]],[[-5828]],[[0]],[[-930]],[[0]],[[-62]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
