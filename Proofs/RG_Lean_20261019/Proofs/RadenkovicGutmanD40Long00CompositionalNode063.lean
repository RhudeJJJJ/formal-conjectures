/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode047
import Proofs.RadenkovicGutmanD40Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e063 : NestedArithmetic.Expr 3 := .times e047 e056
noncomputable def p063 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[0,240],[240]],[[0,0],[0]],[[3600,1040],[1040]],[[0,0],[0]],[[24000,1280],[1280]],[[0,0],[0]],[[62320,560],[560]],[[0,0],[0]],[[84480,80],[80]],[[0]],[[66240]],[[0]],[[31040]],[[0]],[[8560]],[[0]],[[1280]],[[0]],[[80]]]
theorem step063 : p063=NestedArithmetic.mul p047 p056 := by decide +kernel
#print axioms step063
theorem h063 : NestedArithmetic.compile e063=p063 := StagedExprCompile.compile_times e063 e047 e056 p047 p056 p063 rfl h047 h056 step063
#print axioms h063
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
