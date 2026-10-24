/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode090
import Proofs.RadenkovicGutmanD2Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e090 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-144,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1296,-1296,0],[-1296,-1212,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-33804,-14364,0],[-14364,-3928,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-328428,-67608,0],[-67608,-6268,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1731648,-178500,0],[-178500,-5272,0],[0,0]],[[0,0,0],[0,0],[0]],[[-5751772,-294136,0],[-294136,-2224],[0]],[[0,0,0],[0,0],[0]],[[-13000212,-317076,0],[-317076,-296],[0]],[[0,0,0],[0,0],[0]],[[-20897832,-226096,0],[-226096,100],[0]],[[0,0,0],[0,0],[0]],[[-24502592,-103576,0],[-103576,40],[0]],[[0,0,0],[0,0],[0]],[[-21197668,-26816,0],[-26816,4],[0]],[[0,0],[0]],[[-13507304,-1396],[-1396]],[[0,0],[0]],[[-6210088,1480],[1480]],[[0,0],[0]],[[-1935280,508],[508]],[[0,0],[0]],[[-324516,72],[72]],[[0,0],[0]],[[20924,4],[4]],[[0]],[[28728]],[[0]],[[8208]],[[0]],[[1268]],[[0]],[[108]],[[0]],[[4]]]
theorem step102 : p102=NestedHorner.add p090 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e090 e101 p090 p101 p102 rfl h090 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
