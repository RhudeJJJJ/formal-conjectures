/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode075
import Proofs.RadenkovicGutmanD24Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,576]],[[0,0],[0,0,0],[0,0]],[[0,0,5184],[0,10368,10368],[5184,10368]],[[0,0,0],[0,0,0],[0,0]],[[-46656,171072,91584],[171072,276480,27648],[91584,27648]],[[0,0,0],[0,0,0],[0,0]],[[590976,2752704,401472],[2752704,1300608,25344],[401472,25344]],[[0,0,0],[0,0,0],[0,0]],[[16656192,15857856,823680],[15857856,2767104,9216],[823680,9216]],[[0,0,0],[0,0,0],[0,0]],[[128359296,48813696,946944],[48813696,3276288,1152],[946944,1152]],[[0,0,0],[0,0],[0]],[[534089664,93475008,654336],[93475008,2329344],[654336]],[[0,0,0],[0,0],[0]],[[1432108800,119996352,277056],[119996352,1014912],[277056]],[[0,0,0],[0,0],[0]],[[2687437440,107470080,70272],[107470080,264960],[70272]],[[0,0,0],[0,0],[0]],[[3696432768,68504256,9792],[68504256,38016],[9792]],[[0,0,0],[0,0],[0]],[[3831649920,31252032,576],[31252032,2304],[576]],[[0,0],[0]],[[3043503360,10123776],[10123776]],[[0,0],[0]],[[1868849280,2272320],[2272320]],[[0,0],[0]],[[889308288,335808],[335808]],[[0,0],[0]],[[326764224,29376],[29376]],[[0,0],[0]],[[91742976,1152],[1152]],[[0]],[[19301760]],[[0]],[[2943360]],[[0]],[[307008]],[[0]],[[19584]],[[0]],[[576]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
