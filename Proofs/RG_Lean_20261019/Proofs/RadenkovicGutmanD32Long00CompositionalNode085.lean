/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode073
import Proofs.RadenkovicGutmanD32Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-2304,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-20736,-241920,0],[-241920,-57408,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4200768,-3447360,0],[-3447360,-392320,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-65136960,-20958336,0],[-20958336,-1219648,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-463480320,-71890880,0],[-71890880,-2018944,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1967142976,-155502208,0],[-155502208,-1911040,0],[0,0]],[[0,0,0],[0,0],[0]],[[-5562497728,-224976576,0],[-224976576,-1060736],[0]],[[0,0,0],[0,0],[0]],[[-11132220800,-225222912,0],[-225222912,-340544],[0]],[[0,0,0],[0,0],[0]],[[-16362498560,-158887552,0],[-158887552,-58496],[0]],[[0,0,0],[0,0],[0]],[[-18086213056,-79448576,0],[-79448576,-4160],[0]],[[0,0,0],[0,0],[0]],[[-15258656128,-27964608,0],[-27964608,0],[0]],[[0,0],[0]],[[-9906175360,-6769280],[-6769280]],[[0,0],[0]],[[-4960971520,-1072064],[-1072064]],[[0,0],[0]],[[-1910031296,-99968],[-99968]],[[0,0],[0]],[[-559695808,-4160],[-4160]],[[0,0],[0]],[[-122467200,0],[0]],[[0]],[[-19362560]],[[0]],[[-2088256]],[[0]],[[-137408]],[[0]],[[-4160]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
