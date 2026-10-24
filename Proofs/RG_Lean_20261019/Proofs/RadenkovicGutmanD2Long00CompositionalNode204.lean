/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode063
import Proofs.RadenkovicGutmanD2Long00CompositionalNode203
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e063 e203
noncomputable def p204 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-40,0],[0,0]],[[0,0],[0,0]],[[-342,0],[0,0]],[[0,0],[0,0]],[[-1634,0],[0,0]],[[0,0],[0,0]],[[-4786,0],[0,0]],[[0,0],[0,0]],[[-8872,-2],[-2,0]],[[0,0],[0,0]],[[-10372,-22],[-22,0]],[[0,0],[0,0]],[[-7370,-88],[-88,0]],[[0,0],[0,0]],[[-2912,-156],[-156,0]],[[0,0],[0,0]],[[-516,-118],[-118,0]],[[0,0],[0,0]],[[-18,-30],[-30,-2]],[[0],[0,0]],[[0],[0,-2]]]
theorem step204 : p204=NestedArithmetic.mul p063 p203 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e063 e203 p063 p203 p204 rfl h063 h203 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
