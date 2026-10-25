/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode035
import Proofs.RadenkovicGutmanD16Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-2304],[0,-4608,1344],[-2304,1344]],[[0,0,0],[0,0,0],[0,0]],[[0,-63936,-7872],[-63936,8448,5824],[-7872,5824]],[[0,0,0],[0,0,0],[0,0]],[[-404352,-366336,16832],[-366336,203008,7168],[16832,7168]],[[0,0,0],[0,0,0],[0,0]],[[-3131136,-29952,116608],[-29952,700928,3136],[116608,3136]],[[0,0,0],[0,0,0],[0,0]],[[-3829248,4959872,225472],[4959872,1129216,448],[225472,448]],[[0,0,0],[0,0],[0]],[[45497088,18412160,220928],[18412160,1011712],[220928]],[[0,0,0],[0,0],[0]],[[268142208,34940672,122176],[34940672,530176],[122176]],[[0,0,0],[0,0],[0]],[[765961216,41610624,38528],[41610624,161280],[38528]],[[0,0,0],[0,0],[0]],[[1411812352,33312192,6464],[33312192,26368],[6464]],[[0,0,0],[0,0],[0]],[[1837354624,18407872,448],[18407872,1792],[448]],[[0,0],[0]],[[1760520064,7042496],[7042496]],[[0,0],[0]],[[1269029504,1832320],[1832320]],[[0,0],[0]],[[694932992,309440],[309440]],[[0,0],[0]],[[289410048,30592],[30592]],[[0,0],[0]],[[90996608,1344],[1344]],[[0]],[[21232896]],[[0]],[[3562496]],[[0]],[[406144]],[[0]],[[28160]],[[0]],[[896]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
