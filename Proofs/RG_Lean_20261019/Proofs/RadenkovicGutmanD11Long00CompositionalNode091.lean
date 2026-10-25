/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode090
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e091 : NestedArithmetic.Expr 3 := .scaled (-1) e090
noncomputable def p091 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,363],[0,363]],[[0,0,0],[0,0,0],[0,0]],[[0,3267,5445],[3267,17424,1639],[5445,1639]],[[0,0,0],[0,0,0],[0,0]],[[58806,203148,42339],[203148,131604,2222],[42339,2222]],[[0,0,0],[0,0,0],[0,0]],[[2049300,1916442,131450],[1916442,397540,1199],[131450,1199]],[[0,0,0],[0,0,0],[0,0]],[[21264012,8347108,213917],[8347108,633996,275],[213917,275]],[[0,0,0],[0,0,0],[0,0]],[[114306192,21247754,201058],[21247754,589336,22],[201058,22]],[[0,0,0],[0,0],[0]],[[383496366,34981826,113091],[34981826,331364],[113091]],[[0,0,0],[0,0],[0]],[[879513932,39253500,37994],[39253500,112772],[37994]],[[0,0,0],[0,0],[0]],[[1452478016,30862689,7271],[30862689,22308],[7271]],[[0,0,0],[0,0],[0]],[[1783355178,17204649,693],[17204649,2288],[693]],[[0,0,0],[0,0],[0]],[[1660585058,6792401,22],[6792401,88],[22]],[[0,0],[0]],[[1186383418,1870880],[1870880]],[[0,0],[0]],[[653698584,347479],[347479]],[[0,0],[0]],[[277619188,40722],[40722]],[[0,0],[0]],[[90268970,2629],[2629]],[[0,0],[0]],[[22159280,66],[66]],[[0]],[[4008752]],[[0]],[[513458]],[[0]],[[43472]],[[0]],[[2134]],[[0]],[[44]]]
theorem step091 : p091=NestedHorner.scale (-1) p090 := by decide +kernel
#print axioms step091
theorem h091 : NestedArithmetic.compile e091=p091 := StagedExprCompile.compile_scaled (-1) e091 e090 p090 p091 rfl h090 step091
#print axioms h091
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
