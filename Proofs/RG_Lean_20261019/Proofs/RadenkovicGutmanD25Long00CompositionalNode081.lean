/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode079
import Proofs.RadenkovicGutmanD25Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-33750,0],[-33750,-5625,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-556875,-489375,0],[-489375,-48750,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-9095625,-3015000,0],[-3015000,-165625,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-66082500,-10446875,0],[-10446875,-286250,0],[0,0]],[[0,0,0],[0,0],[0]],[[-283903125,-22770000,0],[-22770000,-277500],[0]],[[0,0,0],[0,0],[0]],[[-809455625,-33135625,0],[-33135625,-156250],[0]],[[0,0,0],[0,0],[0]],[[-1629858750,-33322500,0],[-33322500,-50625],[0]],[[0,0,0],[0,0],[0]],[[-2406947500,-23592500,0],[-23592500,-8750],[0]],[[0,0,0],[0,0],[0]],[[-2670586875,-11831250,0],[-11831250,-625],[0]],[[0,0],[0]],[[-2260083750,-4174375],[-4174375]],[[0,0],[0]],[[-1471106250,-1012500],[-1012500]],[[0,0],[0]],[[-738355000,-160625],[-160625]],[[0,0],[0]],[[-284816875,-15000],[-15000]],[[0,0],[0]],[[-83598125,-625],[-625]],[[0]],[[-18318750]],[[0]],[[-2900000]],[[0]],[[-313125]],[[0]],[[-20625]],[[0]],[[-625]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
