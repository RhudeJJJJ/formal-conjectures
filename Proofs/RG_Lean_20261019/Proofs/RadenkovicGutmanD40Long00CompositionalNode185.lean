/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode184
import Proofs.RadenkovicGutmanD40Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[40,0],[0]],[[0,0],[0]],[[640,0],[0]],[[0,0],[0]],[[4280,0],[0]],[[0,0],[0]],[[15520,0],[0]],[[0,0],[0]],[[33120,0],[0]],[[0,0],[0]],[[42240,40],[40]],[[0,0],[0]],[[31160,280],[280]],[[0,0],[0]],[[12000,640],[640]],[[0,0],[0]],[[1800,520],[520]],[[0,0],[0]],[[0,120],[120]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
