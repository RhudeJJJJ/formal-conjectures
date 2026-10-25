/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode113
import Proofs.RadenkovicGutmanD31Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,961]],[[0,0],[0,0,0],[0,0]],[[0,0,8649],[0,0,17298],[8649,17298]],[[0,0,0],[0,0,0],[0,0]],[[77841,155682,152799],[155682,311364,46128],[152799,46128]],[[0,0,0],[0,0,0],[0,0]],[[2750382,3165534,669817],[3165534,1660608,42284],[669817,42284]],[[0,0,0],[0,0,0],[0,0]],[[36351747,19771614,1374230],[19771614,3736368,15376],[1374230,15376]],[[0,0,0],[0,0,0],[0,0]],[[237737946,63748896,1579884],[63748896,4612800,1922],[1579884,1922]],[[0,0,0],[0,0],[0]],[[932305501,126334982,1091696],[126334982,3405784],[1091696]],[[0,0,0],[0,0],[0]],[[2437730260,166973750,462241],[166973750,1537600],[462241]],[[0,0,0],[0,0],[0]],[[4522986862,153563956,117242],[153563956,415152],[117242]],[[0,0,0],[0,0],[0]],[[6189395458,100359152,16337],[100359152,61504],[16337]],[[0,0,0],[0,0],[0]],[[6401520832,46887190,961],[46887190,3844],[961]],[[0,0],[0]],[[5080153520,15539370],[15539370]],[[0,0],[0]],[[3118406560,3565310],[3565310]],[[0,0],[0]],[[1483766702,538160],[538160]],[[0,0],[0]],[[545176261,48050],[48050]],[[0,0],[0]],[[153064236,1922],[1922]],[[0]],[[32203110]],[[0]],[[4910710]],[[0]],[[512213]],[[0]],[[32674]],[[0]],[[961]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
