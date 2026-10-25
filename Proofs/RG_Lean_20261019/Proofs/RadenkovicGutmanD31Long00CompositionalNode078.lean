/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode075
import Proofs.RadenkovicGutmanD31Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,961]],[[0,0],[0,0,0],[0,0]],[[0,0,8649],[0,17298,17298],[8649,17298]],[[0,0,0],[0,0,0],[0,0]],[[-77841,285417,152799],[285417,461280,46128],[152799,46128]],[[0,0,0],[0,0,0],[0,0]],[[985986,4592619,669817],[4592619,2169938,42284],[669817,42284]],[[0,0,0],[0,0,0],[0,0]],[[27789237,26457291,1374230],[26457291,4616644,15376],[1374230,15376]],[[0,0,0],[0,0,0],[0,0]],[[214155006,81440906,1579884],[81440906,5466168,1922],[1579884,1922]],[[0,0,0],[0,0],[0]],[[891076679,155953963,1091696],[155953963,3886284],[1091696]],[[0,0,0],[0,0],[0]],[[2389334300,200202247,462241],[200202247,1693282],[462241]],[[0,0,0],[0,0],[0]],[[4483728090,179303380,117242],[179303380,442060],[117242]],[[0,0,0],[0,0],[0]],[[6167138698,114292691,16337],[114292691,63426],[16337]],[[0,0,0],[0,0],[0]],[[6392735370,52140977,961],[52140977,3844],[961]],[[0,0],[0]],[[5077789460,16890536],[16890536]],[[0,0],[0]],[[3117993330,3791145],[3791145]],[[0,0],[0]],[[1483724418,560263],[560263]],[[0,0],[0]],[[545174339,49011],[49011]],[[0,0],[0]],[[153064236,1922],[1922]],[[0]],[[32203110]],[[0]],[[4910710]],[[0]],[[512213]],[[0]],[[32674]],[[0]],[[961]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
