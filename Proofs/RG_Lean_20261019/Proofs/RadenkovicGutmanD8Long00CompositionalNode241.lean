/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode240
import Proofs.RadenkovicGutmanD8Long00CompositionalNode001
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e241 : NestedArithmetic.Expr 3 := .times e240 e001
noncomputable def p241 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,0],[0,0],[0,0]],[[64,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2112,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[32064,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[296960,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1875840,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[8560448,64,0],[64,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[29165248,1536,0],[1536,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[75607552,16448,0],[16448,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[150641280,103680,0],[103680,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[231432576,427456,0],[427456,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[273468096,1211520,0],[1211520,64,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[246471424,2415872,0],[2415872,896,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[166897536,3412224,0],[3412224,5184,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[82888256,3393088,0],[3393088,16000,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[29071680,2331648,0],[2331648,28416,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[6766848,1069760,0],[1069760,29312,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[931392,308736,0],[308736,16960,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[57024,50112,0],[50112,4992,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,3456,0],[3456,576,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,0],[0,0]]]
theorem step241 : p241=NestedArithmetic.mul p240 p001 := by decide +kernel
#print axioms step241
theorem h241 : NestedArithmetic.compile e241=p241 := StagedExprCompile.compile_times e241 e240 e001 p240 p001 p241 rfl h240 h001 step241
#print axioms h241
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
