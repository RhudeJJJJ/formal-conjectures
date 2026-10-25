/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode174
import Proofs.RadenkovicGutmanD42Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-80],[0]],[[0,0],[0]],[[-1360,0],[0,0]],[[0,0],[0,0]],[[-9760,0],[0,0]],[[0,0],[0,0]],[[-38480,0],[0,0]],[[0,0],[0,0]],[[-90880,0],[0,0]],[[0,0],[0,0]],[[-131520,-80],[-80,0]],[[0,0],[0,0]],[[-114400,-640],[-640,0]],[[0,0],[0,0]],[[-55760,-1760],[-1760,0]],[[0,0],[0,0]],[[-12720,-1920],[-1920,0]],[[0,0],[0,0]],[[-720,-720],[-720,0]],[[0],[0,0]],[[0],[0,-80]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
