/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode217
import Proofs.RadenkovicGutmanD28Long00CompositionalNode219
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e220 : NestedArithmetic.Expr 3 := .times e217 e219
noncomputable def p220 : NestedHorner.Poly 3 := [[[-1568],[0],[0]],[[0,0],[0,0],[0]],[[-48608,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-691488,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-5983488,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-35195328,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-148981952,-2352,0],[-2352,0],[0]],[[0,0,0],[0,0],[0]],[[-468689312,-52528,0],[-52528,0],[0]],[[0,0,0],[0,0],[0]],[[-1115928352,-521360,0],[-521360,0],[0]],[[0,0,0],[0,0],[0]],[[-2028778752,-3030944,0],[-3030944,0],[0]],[[0,0,0],[0,0],[0]],[[-2820799072,-11453456,0],[-11453456,0],[0]],[[0,0,0],[0,0],[0]],[[-2984222304,-29524656,-784],[-29524656,-1568],[-784]],[[0,0,0],[0,0],[0]],[[-2372474944,-53026624,-10976],[-53026624,-21952],[-10976]],[[0,0,0],[0,0],[0]],[[-1386579264,-66590608,-63504],[-66590608,-127008],[-63504]],[[0,0,0],[0,0],[0]],[[-574527744,-57798832,-196000],[-57798832,-392000],[-196000]],[[0,0,0],[0,0],[0]],[[-158717664,-33672800,-348096],[-33672800,-696192],[-348096]],[[0,0,0],[0,0],[0]],[[-26036640,-12439728,-359072],[-12439728,-718144],[-359072]],[[0,0,0],[0,0],[0]],[[-1905120,-2603664,-207760],[-2603664,-415520],[-207760]],[[0,0,0],[0,0],[0]],[[0,-232848,-61152],[-232848,-122304],[-61152]],[[0,0,0],[0,0],[0]],[[0,0,-7056],[0,-14112],[-7056]]]
theorem step220 : p220=NestedArithmetic.mul p217 p219 := by decide +kernel
#print axioms step220
theorem h220 : NestedArithmetic.compile e220=p220 := StagedExprCompile.compile_times e220 e217 e219 p217 p219 p220 rfl h217 h219 step220
#print axioms h220
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
