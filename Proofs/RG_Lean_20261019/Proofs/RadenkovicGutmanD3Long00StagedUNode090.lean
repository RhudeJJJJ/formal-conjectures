/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode087
import Proofs.RadenkovicGutmanD3Long00StagedUNode089
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .plus e087 e089
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,54],[0,54,-6]],[[0,0,0],[0,0,0],[0,0]],[[0,0,648],[0,2187,144],[648,144]],[[0,0,0],[0,0,0],[0,0]],[[1215,17901,4482],[17901,14418,78],[4482,78]],[[0,0,0],[0,0,0],[0,0]],[[139887,176094,12708],[176094,38907,-42],[12708,-42]],[[0,0,0],[0,0,0],[0,0]],[[1672326,760239,19170],[760239,56070,-36],[19170,-36]],[[0,0,0],[0,0,0],[0,0]],[[9441783,1906188,16782],[1906188,47148,-6],[16782,-6]],[[0,0,0],[0,0],[0]],[[32454681,3095361,8742],[3095361,23718],[8742]],[[0,0,0],[0,0],[0]],[[75614478,3435390,2664],[3435390,7011],[2664]],[[0,0,0],[0,0],[0]],[[126482472,2679018,438],[2679018,1122],[438]],[[0,0,0],[0,0],[0]],[[157181373,1484988,30],[1484988,75],[30]],[[0,0,0],[0,0],[0]],[[148187862,584307,0],[584307,0],[0]],[[0,0],[0]],[[107297238,160782],[160782]],[[0,0],[0]],[[60008064,29919],[29919]],[[0,0],[0]],[[25922097,3528],[3528]],[[0,0],[0]],[[8598477,231],[231]],[[0,0],[0]],[[2162190,6],[6]],[[0]],[[403092]],[[0]],[[53691]],[[0]],[[4797]],[[0]],[[255]],[[0]],[[6]]]
theorem step090 : p090=NestedHorner.add p087 p089 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_plus e090 e087 e089 p087 p089 p090 rfl h087 h089 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
