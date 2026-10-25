/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode236
import Proofs.RadenkovicGutmanD12Long00CompositionalNode238
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e239 : NestedArithmetic.Expr 3 := .plus e236 e238
noncomputable def p239 : NestedHorner.Poly 3 := [[[-144],[0],[0]],[[0,0],[0,0],[0]],[[-4752,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-72144,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-668160,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4220640,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-19261008,-144,0],[-144,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-65621808,-3456,0],[-3456,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-170116992,-37008,0],[-37008,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-338942880,-233280,0],[-233280,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-520723296,-961776,0],[-961776,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-615303216,-2725920,0],[-2725920,-144,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-554560704,-5435712,0],[-5435712,-2016,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-375519456,-7677504,0],[-7677504,-11664,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-186498576,-7634448,0],[-7634448,-36000,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-65411280,-5246208,0],[-5246208,-63936,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-15225408,-2406960,0],[-2406960,-65952,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2095632,-694656,0],[-694656,-38160,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-128304,-112752,0],[-112752,-11232,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-7776,0],[-7776,-1296,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,0],[0,0]]]
theorem step239 : p239=NestedHorner.add p236 p238 := by decide +kernel
#print axioms step239
theorem h239 : NestedArithmetic.compile e239=p239 := StagedExprCompile.compile_plus e239 e236 e238 p236 p238 p239 rfl h236 h238 step239
#print axioms h239
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
