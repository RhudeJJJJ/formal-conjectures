/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode240
import Proofs.RadenkovicGutmanD14Long00CompositionalNode001
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e241 : NestedArithmetic.Expr 3 := .times e240 e001
noncomputable def p241 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,0],[0,0],[0,0]],[[196,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[6468,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[98196,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[909440,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[5744760,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[26216372,196,0],[196,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[89318572,4704,0],[4704,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[231548128,50372,0],[50372,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[461338920,317520,0],[317520,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[708762264,1309084,0],[1309084,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[837496044,3710280,0],[3710280,196,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[754818736,7398608,0],[7398608,2744,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[511123704,10449936,0],[10449936,15876,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[253845284,10391332,0],[10391332,49000,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[89032020,7140672,0],[7140672,87024,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[20723472,3276140,0],[3276140,89768,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2852388,945504,0],[945504,51940,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[174636,153468,0],[153468,15288,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,10584,0],[10584,1764,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,0],[0,0]]]
theorem step241 : p241=NestedArithmetic.mul p240 p001 := by decide +kernel
#print axioms step241
theorem h241 : NestedArithmetic.compile e241=p241 := StagedExprCompile.compile_times e241 e240 e001 p240 p001 p241 rfl h240 h001 step241
#print axioms h241
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
