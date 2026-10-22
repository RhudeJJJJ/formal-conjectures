/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
namespace Gebendorfer.RadenkovicGutman.DegreeOneNormPack20
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def vDirect : NestedHorner.Poly 3 := [[[0,0,0,0,0]],[[0,0,0,0,0]],[[0,0,0,0,0]],[[0,0,0,0,0]],[[0,0,0,0,0]],[[0,0,0,0,0]],[[0,0,576,0,0]],[[0,0,0,0,0]],[[0,13824,6432,0,0]],[[0,0,0,0,0]],[[82944,193536,30628,0,0]],[[0,0,0,0,0]],[[1396224,1204704,82368,0,0]],[[0,0,0,0]],[[10711872,4430096,139832,0]],[[0,0,0,0]],[[49832256,10789088,158408,0]],[[0,0,0,0]],[[157789840,18487144,123172,0]],[[0,0,0,0]],[[361876640,23102344,66448,0]],[[0,0,0,0]],[[624480528,21523008,24772,0]],[[0,0,0]],[[831463856,15141632,6248]],[[0,0,0]],[[868760436,8089448,1016]],[[0,0,0]],[[720470664,3278888,96]],[[0,0,0]],[[477581500,1000072,4]],[[0,0,0]],[[253892648,225528,0]],[[0,0]],[[108232156,36432]],[[0,0]],[[36853296,3984]],[[0,0]],[[9940408,264]],[[0,0]],[[2094272,8]],[[0,0]],[[337020,0]],[[0]],[[39976]],[[0]],[[3292]],[[0]],[[168]],[[0]],[[4]],[[0]],[[0]]]
theorem vDirect_checked : NestedArithmetic.accepts (NestedClassPolynomials.programV 1 1 4) vDirect=true := by decide +kernel
#print axioms vDirect_checked
end Gebendorfer.RadenkovicGutman.DegreeOneNormPack20
