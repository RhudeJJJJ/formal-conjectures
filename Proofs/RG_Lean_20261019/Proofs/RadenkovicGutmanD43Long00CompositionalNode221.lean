/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode220
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e221 : NestedArithmetic.Expr 3 := .scaled (-1) e220
noncomputable def p221 : NestedHorner.Poly 3 := [[[3698],[0],[0]],[[0,0],[0,0],[0]],[[114638,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1630818,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[14111568,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[83005308,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[351361772,5547,0],[5547,0],[0]],[[0,0,0],[0,0],[0]],[[1105365482,123883,0],[123883,0],[0]],[[0,0,0],[0,0],[0]],[[2631825922,1229585,0],[1229585,0],[0]],[[0,0,0],[0,0],[0]],[[4784709072,7148234,0],[7148234,0],[0]],[[0,0,0],[0,0],[0]],[[6652624342,27012041,0],[27012041,0],[0]],[[0,0,0],[0,0],[0]],[[7038044694,69631491,1849],[69631491,3698],[1849]],[[0,0,0],[0,0],[0]],[[5595288484,125058964,25886],[125058964,51772],[25886]],[[0,0,0],[0,0],[0]],[[3270134004,157048513,149769],[157048513,299538],[149769]],[[0,0,0],[0,0],[0]],[[1354976784,136313827,462250],[136313827,924500],[462250]],[[0,0,0],[0,0],[0]],[[374322654,79414550,820956],[79414550,1641912],[820956]],[[0,0,0],[0,0],[0]],[[61405290,29338083,846842],[29338083,1693684],[846842]],[[0,0,0],[0,0],[0]],[[4493070,6140529,489985],[6140529,979970],[489985]],[[0,0,0],[0,0],[0]],[[0,549153,144222],[549153,288444],[144222]],[[0,0,0],[0,0],[0]],[[0,0,16641],[0,33282],[16641]]]
theorem step221 : p221=NestedHorner.scale (-1) p220 := by decide +kernel
#print axioms step221
theorem h221 : NestedArithmetic.compile e221=p221 := StagedExprCompile.compile_scaled (-1) e221 e220 p220 p221 rfl h220 step221
#print axioms h221
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
