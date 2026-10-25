/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode099
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e103 : NestedArithmetic.Expr 3 := .scaled (-1) e099
noncomputable def p103 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1944],[0,-1944,576]],[[0,0,0],[0,0,0],[0,0]],[[0,0,-23328],[0,-80028,1836],[-23328,1836]],[[0,0,0],[0,0,0],[0,0]],[[-84564,-651240,-127332],[-651240,-393876,16812],[-127332,16812]],[[0,0,0],[0,0,0],[0,0]],[[-5758128,-5749380,-267948],[-5749380,-677844,20232],[-267948,20232]],[[0,0,0],[0,0,0],[0,0]],[[-62547228,-22158036,-246240],[-22158036,-299412,8316],[-246240,8316]],[[0,0,0],[0,0,0],[0,0]],[[-328860540,-48772188,-35892],[-48772188,528264,1116],[-35892,1116]],[[0,0,0],[0,0],[0]],[[-1056486744,-67217940,118728],[-67217940,859896],[118728]],[[0,0,0],[0,0],[0]],[[-2291101236,-59332284,105516],[-59332284,550620],[105516]],[[0,0,0],[0,0],[0]],[[-3532192920,-31984272,40032],[-31984272,183708],[40032]],[[0,0,0],[0,0],[0]],[[-3980326356,-7875972,7380],[-7875972,31500],[7380]],[[0,0,0],[0,0],[0]],[[-3317727204,1895544,540],[1895544,2196],[540]],[[0,0],[0]],[[-2040140664,2362104],[2362104]],[[0,0],[0]],[[-904283856,921636],[921636]],[[0,0],[0]],[[-269305812,194544],[194544]],[[0,0],[0]],[[-40821696,22212],[22212]],[[0,0],[0]],[[4706316,1080],[1080]],[[0]],[[4379400]],[[0]],[[1185156]],[[0]],[[177840]],[[0]],[[14832]],[[0]],[[540]]]
theorem step103 : p103=NestedHorner.scale (-1) p099 := by decide +kernel
#print axioms step103
theorem h103 : NestedArithmetic.compile e103=p103 := StagedExprCompile.compile_scaled (-1) e103 e099 p099 p103 rfl h099 step103
#print axioms h103
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
