/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode182
import Proofs.RadenkovicGutmanD2Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e183 : NestedArithmetic.Expr 3 := .times e182 e003
noncomputable def p183 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[2,0],[0]],[[0,0],[0]],[[32,0],[0]],[[0,0],[0]],[[214,0],[0]],[[0,0],[0]],[[776,0],[0]],[[0,0],[0]],[[1656,0],[0]],[[0,0],[0]],[[2112,2],[2]],[[0,0],[0]],[[1558,14],[14]],[[0,0],[0]],[[600,32],[32]],[[0,0],[0]],[[90,26],[26]],[[0,0],[0]],[[0,6],[6]]]
theorem step183 : p183=NestedArithmetic.mul p182 p003 := by decide +kernel
#print axioms step183
theorem h183 : NestedArithmetic.compile e183=p183 := StagedExprCompile.compile_times e183 e182 e003 p182 p003 p183 rfl h182 h003 step183
#print axioms h183
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
