/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode095
import Proofs.RadenkovicGutmanD30Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2160,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-19440,-19440,0],[-19440,-18720,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-511920,-220320,0],[-220320,-63600,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5054400,-1069200,0],[-1069200,-109920,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-27238320,-2944800,0],[-2944800,-106560,0],[0,0]],[[0,0,0],[0,0],[0]],[[-93086160,-5148240,0],[-5148240,-60000],[0]],[[0,0,0],[0,0],[0]],[[-218274720,-6043200,0],[-6043200,-19440],[0]],[[0,0,0],[0,0],[0]],[[-368036160,-4902240,0],[-4902240,-3360],[0]],[[0,0,0],[0,0],[0]],[[-459547920,-2779200,0],[-2779200,-240],[0]],[[0,0,0],[0,0],[0]],[[-432852000,-1097040,0],[-1097040,0],[0]],[[0,0],[0]],[[-310822560,-295200],[-295200]],[[0,0],[0]],[[-170856960,-51600],[-51600]],[[0,0],[0]],[[-71743440,-5280],[-5280]],[[0,0],[0]],[[-22803600,-240],[-240]],[[0,0],[0]],[[-5387040,0],[0]],[[0]],[[-915840]],[[0]],[[-105840]],[[0]],[[-7440]],[[0]],[[-240]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
