/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode089
import Proofs.RadenkovicGutmanD14Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1176],[0,1176,-336]],[[0,0,0],[0,0,0],[0,0]],[[0,0,14112],[0,47628,-868],[14112,-868]],[[0,0,0],[0,0,0],[0,0]],[[43092,387072,78204],[387072,236376,-9492],[78204,-9492]],[[0,0,0],[0,0,0],[0,0]],[[3284820,3424680,168644],[3424680,414876,-11592],[168644,-11592]],[[0,0,0],[0,0,0],[0,0]],[[36070272,13237308,164304],[13237308,208376,-4788],[164304,-4788]],[[0,0,0],[0,0,0],[0,0]],[[190432956,29274056,41356],[29274056,-269696,-644],[41356,-644]],[[0,0,0],[0,0],[0]],[[613451020,40681228,-56840],[40681228,-472360],[-56840]],[[0,0,0],[0,0],[0]],[[1334139856,36488872,-56868],[36488872,-306852],[-56868]],[[0,0,0],[0,0],[0]],[[2064783056,20416144,-22288],[20416144,-102872],[-22288]],[[0,0,0],[0,0],[0]],[[2340083732,5808516,-4172],[5808516,-17668],[-4172]],[[0,0,0],[0,0],[0]],[[1967930160,-491680,-308],[-491680,-1232],[-308]],[[0,0],[0]],[[1227823744,-1154356],[-1154356]],[[0,0],[0]],[[558574968,-480844],[-480844]],[[0,0],[0]],[[175928228,-103964],[-103964]],[[0,0],[0]],[[32317964,-12012],[-12012]],[[0,0],[0]],[[113792,-588],[-588]],[[0]],[[-1848784]],[[0]],[[-567028]],[[0]],[[-88956]],[[0]],[[-7588]],[[0]],[[-280]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
