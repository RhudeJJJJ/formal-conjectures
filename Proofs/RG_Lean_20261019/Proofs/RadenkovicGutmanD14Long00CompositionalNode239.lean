/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode236
import Proofs.RadenkovicGutmanD14Long00CompositionalNode238
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e239 : NestedArithmetic.Expr 3 := .plus e236 e238
noncomputable def p239 : NestedHorner.Poly 3 := [[[-196],[0],[0]],[[0,0],[0,0],[0]],[[-6468,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-98196,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-909440,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5744760,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-26216372,-196,0],[-196,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-89318572,-4704,0],[-4704,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-231548128,-50372,0],[-50372,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-461338920,-317520,0],[-317520,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-708762264,-1309084,0],[-1309084,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-837496044,-3710280,0],[-3710280,-196,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-754818736,-7398608,0],[-7398608,-2744,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-511123704,-10449936,0],[-10449936,-15876,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-253845284,-10391332,0],[-10391332,-49000,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-89032020,-7140672,0],[-7140672,-87024,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-20723472,-3276140,0],[-3276140,-89768,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2852388,-945504,0],[-945504,-51940,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-174636,-153468,0],[-153468,-15288,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-10584,0],[-10584,-1764,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,0],[0,0]]]
theorem step239 : p239=NestedHorner.add p236 p238 := by decide +kernel
#print axioms step239
theorem h239 : NestedArithmetic.compile e239=p239 := StagedExprCompile.compile_plus e239 e236 e238 p236 p238 p239 rfl h236 h238 step239
#print axioms h239
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
