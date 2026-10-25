/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .scaled (-1) e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,3969],[0,7938],[3969]],[[0,0,0],[0,0],[0]],[[0,130977,34398],[130977,68796],[34398]],[[0,0,0],[0,0],[0]],[[1071630,1464561,116865],[1464561,233730],[116865]],[[0,0,0],[0,0],[0]],[[14645610,6997347,201978],[6997347,403956],[201978]],[[0,0,0],[0,0],[0]],[[89278686,18940950,195804],[18940950,391608],[195804]],[[0,0,0],[0,0],[0]],[[323171856,32511843,110250],[32511843,220500],[110250]],[[0,0,0],[0,0],[0]],[[779950836,37457217,35721],[37457217,71442],[35721]],[[0,0,0],[0,0],[0]],[[1334517156,29827476,6174],[29827476,12348],[6174]],[[0,0,0],[0,0],[0]],[[1678625046,16607619,441],[16607619,882],[441]],[[0,0],[0]],[[1586699478,6442569],[6442569]],[[0,0],[0]],[[1141188048,1704906],[1704906]],[[0,0],[0]],[[627709698,293265],[293265]],[[0,0],[0]],[[263637738,29547],[29547]],[[0,0],[0]],[[83802348,1323],[1323]],[[0]],[[19797372]],[[0]],[[3365712]],[[0]],[[388962]],[[0]],[[27342]],[[0]],[[882]]]
theorem step077 : p077=NestedHorner.scale (-1) p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_scaled (-1) e077 e076 p076 p077 rfl h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
