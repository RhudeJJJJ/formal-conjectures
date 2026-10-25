/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode033
import Proofs.RadenkovicGutmanD44Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1936]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,34848],[0,34848]],[[0,0,0],[0,0,0],[0,0]],[[-156816,0,156816],[0,627264,92928],[156816,92928]],[[0,0,0],[0,0,0],[0,0]],[[-2718144,2822688,836352],[2822688,3345408,85184],[836352,85184]],[[0,0,0],[0,0,0],[0,0]],[[-8311248,22581504,1881792],[22581504,7527168,30976],[1881792,30976]],[[0,0,0],[0,0,0],[0,0]],[[39494400,80917056,2323200],[80917056,9292800,3872],[2323200,3872]],[[0,0,0],[0,0],[0]],[[376402928,171452160,1715296],[171452160,6861184],[1715296]],[[0,0,0],[0,0],[0]],[[1389474944,238883040,774400],[238883040,3097600],[774400]],[[0,0,0],[0,0],[0]],[[3174215264,230275584,209088],[230275584,836352],[209088]],[[0,0,0],[0,0],[0]],[[5054919232,157342592,30976],[157342592,123904],[30976]],[[0,0,0],[0,0],[0]],[[5912954432,76758528,1936],[76758528,7744],[1936]],[[0,0],[0]],[[5219711552,26542560],[26542560]],[[0,0],[0]],[[3525750272,6350080],[6350080]],[[0,0],[0]],[[1831688320,998976],[998976]],[[0,0],[0]],[[730396656,92928],[92928]],[[0,0],[0]],[[221447424,3872],[3872]],[[0]],[[50099808]],[[0]],[[8185408]],[[0]],[[911856]],[[0]],[[61952]],[[0]],[[1936]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
