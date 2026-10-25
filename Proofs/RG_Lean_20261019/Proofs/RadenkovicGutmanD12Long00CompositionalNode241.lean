/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode240
import Proofs.RadenkovicGutmanD12Long00CompositionalNode001
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e241 : NestedArithmetic.Expr 3 := .times e240 e001
noncomputable def p241 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,0],[0,0],[0,0]],[[144,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[4752,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[72144,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[668160,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[4220640,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[19261008,144,0],[144,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[65621808,3456,0],[3456,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[170116992,37008,0],[37008,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[338942880,233280,0],[233280,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[520723296,961776,0],[961776,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[615303216,2725920,0],[2725920,144,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[554560704,5435712,0],[5435712,2016,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[375519456,7677504,0],[7677504,11664,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[186498576,7634448,0],[7634448,36000,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[65411280,5246208,0],[5246208,63936,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[15225408,2406960,0],[2406960,65952,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2095632,694656,0],[694656,38160,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[128304,112752,0],[112752,11232,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,7776,0],[7776,1296,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,0],[0,0]]]
theorem step241 : p241=NestedArithmetic.mul p240 p001 := by decide +kernel
#print axioms step241
theorem h241 : NestedArithmetic.compile e241=p241 := StagedExprCompile.compile_times e241 e240 e001 p240 p001 p241 rfl h240 h001 step241
#print axioms h241
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
