/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode094
import Proofs.RadenkovicGutmanD3Long00StagedUNode096
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .plus e094 e096
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,54],[0,54,-6]],[[0,0,0],[0,0,0],[0,0]],[[0,0,648],[0,2403,144],[648,144]],[[0,0,0],[0,0,0],[0,0]],[[3159,19845,4482],[19845,16236,78],[4482,78]],[[0,0,0],[0,0,0],[0,0]],[[190593,197640,12708],[197640,44799,-42],[12708,-42]],[[0,0,0],[0,0,0],[0,0]],[[2164968,861651,19170],[861651,65472,-36],[19170,-36]],[[0,0,0],[0,0,0],[0,0]],[[12039255,2173938,16782],[2173938,55056,-6],[16782,-6]],[[0,0,0],[0,0],[0]],[[41082339,3536565,8742],[3536565,27054],[8742]],[[0,0,0],[0,0],[0]],[[95114796,3911004,2664],[3911004,7455],[2664]],[[0,0,0],[0,0],[0]],[[157829220,3018162,438],[3018162,972],[438]],[[0,0,0],[0,0],[0]],[[193935261,1640352,30],[1640352,15],[30]],[[0,0,0],[0,0],[0]],[[179984364,624531,0],[624531,-6],[0]],[[0,0],[0]],[[127558194,162876],[162876]],[[0,0],[0]],[[69323196,27699],[27699]],[[0,0],[0]],[[28825017,2766],[2766]],[[0,0],[0]],[[9085251,123],[123]],[[0,0],[0]],[[2130804,0],[0]],[[0]],[[360000]],[[0]],[[41379]],[[0]],[[2895]],[[0]],[[93]],[[0]],[[0]]]
theorem step097 : p097=NestedHorner.add p094 p096 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_plus e097 e094 e096 p094 p096 p097 rfl h094 h096 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
