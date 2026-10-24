/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode169
import Proofs.RadenkovicGutmanD2Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e170 : NestedArithmetic.Expr 3 := .times e169 e003
noncomputable def p170 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[4,0],[0]],[[0,0],[0]],[[60,0],[0]],[[0,0],[0]],[[376,0],[0]],[[0,0],[0]],[[1276,0],[0]],[[0,0],[0]],[[2544,0],[0]],[[0,0],[0]],[[3028,2],[2]],[[0,0],[0]],[[2088,14],[14]],[[0,0],[0]],[[756,32],[32]],[[0,0],[0]],[[108,26],[26]],[[0,0],[0]],[[0,6],[6]]]
theorem step170 : p170=NestedArithmetic.mul p169 p003 := by decide +kernel
#print axioms step170
theorem h170 : NestedArithmetic.compile e170=p170 := StagedExprCompile.compile_times e170 e169 e003 p169 p003 p170 rfl h169 h003 step170
#print axioms h170
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
