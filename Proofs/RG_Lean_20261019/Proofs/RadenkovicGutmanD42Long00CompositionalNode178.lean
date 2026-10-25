/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode177
import Proofs.RadenkovicGutmanD42Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-80],[0]],[[0,0],[0]],[[-1360,0],[0,0]],[[0,0],[0,0]],[[-9760,0],[0,0]],[[0,0],[0,0]],[[-38480,0],[0,0]],[[0,0],[0,0]],[[-90880,0],[0,0]],[[0,0],[0,0]],[[-131520,-80],[-80,0]],[[0,0],[0,0]],[[-114400,-640],[-640,0]],[[0,0],[0,0]],[[-55760,-1760],[-1760,0]],[[0,0],[0,0]],[[-12720,-1920],[-1920,0]],[[0,0],[0,0]],[[-720,-720],[-720,0]],[[0],[0,0]],[[0],[0,-80]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
