/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode237
import Proofs.RadenkovicGutmanD3Long00StagedUNode001
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e238 : NestedArithmetic.Expr 3 := .times e237 e001
noncomputable def p238 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,0],[0,0],[0,0]],[[9,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[297,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[4509,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[41760,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[263790,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1203813,9,0],[9,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[4101363,216,0],[216,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[10632312,2313,0],[2313,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[21183930,14580,0],[14580,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[32545206,60111,0],[60111,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[38456451,170370,0],[170370,9,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[34660044,339732,0],[339732,126,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[23469966,479844,0],[479844,729,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[11656161,477153,0],[477153,2250,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[4088205,327888,0],[327888,3996,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[951588,150435,0],[150435,4122,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[130977,43416,0],[43416,2385,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[8019,7047,0],[7047,702,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,486,0],[486,81,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,0],[0,0]]]
theorem step238 : p238=NestedArithmetic.mul p237 p001 := by decide +kernel
#print axioms step238
theorem h238 : NestedArithmetic.compile e238=p238 := StagedExprCompile.compile_times e238 e237 e001 p237 p001 p238 rfl h237 h001 step238
#print axioms h238
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
