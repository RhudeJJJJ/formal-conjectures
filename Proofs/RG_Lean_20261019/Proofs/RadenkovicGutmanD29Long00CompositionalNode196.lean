/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode195
import Proofs.RadenkovicGutmanD29Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[116,0],[0]],[[0,0],[0]],[[1740,0],[0]],[[0,0],[0]],[[10904,0],[0]],[[0,0],[0]],[[37004,0],[0]],[[0,0],[0]],[[73776,0],[0]],[[0,0],[0]],[[87812,58],[58]],[[0,0],[0]],[[60552,406],[406]],[[0,0],[0]],[[21924,928],[928]],[[0,0],[0]],[[3132,754],[754]],[[0,0],[0]],[[0,174],[174]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
