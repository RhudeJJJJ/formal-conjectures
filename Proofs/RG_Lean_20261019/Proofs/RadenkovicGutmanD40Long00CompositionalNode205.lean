/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode204
import Proofs.RadenkovicGutmanD40Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[80,0],[0]],[[0,0],[0]],[[1280,0],[0]],[[0,0],[0]],[[8560,0],[0]],[[0,0],[0]],[[31040,0],[0]],[[0,0],[0]],[[66240,0],[0]],[[0,0],[0]],[[84480,80],[80]],[[0,0],[0]],[[62320,560],[560]],[[0,0],[0]],[[24000,1280],[1280]],[[0,0],[0]],[[3600,1040],[1040]],[[0,0],[0]],[[0,240],[240]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
