/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode081
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e084 : NestedArithmetic.Expr 3 := .scaled (-1) e081
noncomputable def p084 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,95256,0],[95256,15876,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1571724,1381212,0],[1381212,137592,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[25671492,8509536,0],[8509536,467460,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[186511248,29485260,0],[29485260,807912,0],[0,0]],[[0,0,0],[0,0],[0]],[[801288180,64266048,0],[64266048,783216],[0]],[[0,0,0],[0,0],[0]],[[2284607556,93521988,0],[93521988,441000],[0]],[[0,0,0],[0,0],[0]],[[4600113336,94049424,0],[94049424,142884],[0]],[[0,0,0],[0,0],[0]],[[6793368624,66587472,0],[66587472,24696],[0]],[[0,0,0],[0,0],[0]],[[7537464396,33392520,0],[33392520,1764],[0]],[[0,0],[0]],[[6378860376,11781756],[11781756]],[[0,0],[0]],[[4152050280,2857680],[2857680]],[[0,0],[0]],[[2083933152,453348],[453348]],[[0,0],[0]],[[803867148,42336],[42336]],[[0,0],[0]],[[235947348,1764],[1764]],[[0]],[[51702840]],[[0]],[[8184960]],[[0]],[[883764]],[[0]],[[58212]],[[0]],[[1764]]]
theorem step084 : p084=NestedHorner.scale (-1) p081 := by decide +kernel
#print axioms step084
theorem h084 : NestedArithmetic.compile e084=p084 := StagedExprCompile.compile_scaled (-1) e084 e081 p081 p084 rfl h081 step084
#print axioms h084
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
