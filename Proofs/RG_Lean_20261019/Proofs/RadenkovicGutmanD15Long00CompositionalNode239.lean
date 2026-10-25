/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode236
import Proofs.RadenkovicGutmanD15Long00CompositionalNode238
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e239 : NestedArithmetic.Expr 3 := .plus e236 e238
noncomputable def p239 : NestedHorner.Poly 3 := [[[-225],[0],[0]],[[0,0],[0,0],[0]],[[-7425,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-112725,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1044000,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6594750,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-30095325,-225,0],[-225,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-102534075,-5400,0],[-5400,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-265807800,-57825,0],[-57825,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-529598250,-364500,0],[-364500,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-813630150,-1502775,0],[-1502775,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-961411275,-4259250,0],[-4259250,-225,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-866501100,-8493300,0],[-8493300,-3150,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-586749150,-11996100,0],[-11996100,-18225,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-291404025,-11928825,0],[-11928825,-56250,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-102205125,-8197200,0],[-8197200,-99900,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-23789700,-3760875,0],[-3760875,-103050,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3274425,-1085400,0],[-1085400,-59625,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-200475,-176175,0],[-176175,-17550,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-12150,0],[-12150,-2025,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,0],[0,0]]]
theorem step239 : p239=NestedHorner.add p236 p238 := by decide +kernel
#print axioms step239
theorem h239 : NestedArithmetic.compile e239=p239 := StagedExprCompile.compile_plus e239 e236 e238 p236 p238 p239 rfl h236 h238 step239
#print axioms h239
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
