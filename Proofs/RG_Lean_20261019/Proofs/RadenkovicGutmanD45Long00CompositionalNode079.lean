/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode033
import Proofs.RadenkovicGutmanD45Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,6075],[0,6075]],[[0,0,0],[0,0,0],[0,0]],[[0,-54675,54675],[-54675,200475,26325],[54675,26325]],[[0,0,0],[0,0,0],[0,0]],[[-820125,601425,382725],[601425,1372950,32400],[382725,32400]],[[0,0,0],[0,0,0],[0,0]],[[-5194125,8456400,1057050],[8456400,3691575,14175],[1057050,14175]],[[0,0,0],[0,0,0],[0,0]],[[2843100,38270475,1532925],[38270475,5204250,2025],[1532925,2025]],[[0,0,0],[0,0],[0]],[[133777575,94757850,1287900],[94757850,4252500],[1287900]],[[0,0,0],[0,0],[0]],[[635908725,148859775,645975],[148859775,2077650],[645975]],[[0,0,0],[0,0],[0]],[[1683119250,158383350,190350],[158383350,597375],[190350]],[[0,0,0],[0,0],[0]],[[2987563500,117711225,30375],[117711225,93150],[30375]],[[0,0,0],[0,0],[0]],[[3815656875,61776675,2025],[61776675,6075],[2025]],[[0,0],[0]],[[3629407500,22781250],[22781250]],[[0,0],[0]],[[2616794100,5771250],[5771250]],[[0,0],[0]],[[1440649800,955800],[955800]],[[0,0],[0]],[[605242125,93150],[93150]],[[0,0],[0]],[[192401325,4050],[4050]],[[0]],[[45453150]],[[0]],[[7727400]],[[0]],[[893025]],[[0]],[[62775]],[[0]],[[2025]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
