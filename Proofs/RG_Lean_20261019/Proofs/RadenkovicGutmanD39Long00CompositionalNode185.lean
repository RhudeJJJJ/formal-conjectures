/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode184
import Proofs.RadenkovicGutmanD39Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[39,0],[0]],[[0,0],[0]],[[624,0],[0]],[[0,0],[0]],[[4173,0],[0]],[[0,0],[0]],[[15132,0],[0]],[[0,0],[0]],[[32292,0],[0]],[[0,0],[0]],[[41184,39],[39]],[[0,0],[0]],[[30381,273],[273]],[[0,0],[0]],[[11700,624],[624]],[[0,0],[0]],[[1755,507],[507]],[[0,0],[0]],[[0,117],[117]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
