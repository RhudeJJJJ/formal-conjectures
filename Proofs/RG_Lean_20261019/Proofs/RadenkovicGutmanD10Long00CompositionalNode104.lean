/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode092
import Proofs.RadenkovicGutmanD10Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-720,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6480,-6480,0],[-6480,-6060,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-169020,-71820,0],[-71820,-19640,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1642140,-338040,0],[-338040,-31340,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-8658240,-892500,0],[-892500,-26360,0],[0,0]],[[0,0,0],[0,0],[0]],[[-28758860,-1470680,0],[-1470680,-11120],[0]],[[0,0,0],[0,0],[0]],[[-65001060,-1585380,0],[-1585380,-1480],[0]],[[0,0,0],[0,0],[0]],[[-104489160,-1130480,0],[-1130480,500],[0]],[[0,0,0],[0,0],[0]],[[-122512960,-517880,0],[-517880,200],[0]],[[0,0,0],[0,0],[0]],[[-105988340,-134080,0],[-134080,20],[0]],[[0,0],[0]],[[-67536520,-6980],[-6980]],[[0,0],[0]],[[-31050440,7400],[7400]],[[0,0],[0]],[[-9676400,2540],[2540]],[[0,0],[0]],[[-1622580,360],[360]],[[0,0],[0]],[[104620,20],[20]],[[0]],[[143640]],[[0]],[[41040]],[[0]],[[6340]],[[0]],[[540]],[[0]],[[20]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
