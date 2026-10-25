/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode043
import Proofs.RadenkovicGutmanD6Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-108],[0,-108,48]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-972,-1620],[-972,-5616,648],[-1620,648,16]],[[0,0,0],[0,0,0],[0,0]],[[-25272,-69660,-6264],[-69660,-18576,3108],[-6264,3108]],[[0,0,0],[0,0,0],[0,0]],[[-862488,-556632,36],[-556632,16848,3972],[36,3972]],[[0,0,0],[0,0,0],[0,0]],[[-8507808,-1964448,37188],[-1964448,163040,2024],[37188,2024]],[[0,0,0],[0,0,0],[0,0]],[[-43396416,-3757488,81876],[-3757488,318832,436],[81876,436]],[[0,0,0],[0,0,0],[0,0]],[[-137724600,-3835680,85668],[-3835680,316944,32],[85668,32]],[[0,0,0],[0,0],[0]],[[-296153096,-1039168,50956],[-1039168,183600],[50956]],[[0,0,0],[0,0],[0]],[[-450602048,2558516,17932],[2558516,64000],[17932]],[[0,0,0],[0,0],[0]],[[-494135672,4028728,3648],[4028728,13120],[3648]],[[0,0,0],[0,0],[0]],[[-388772816,3084104,388],[3084104,1440],[388]],[[0,0,0],[0,0],[0]],[[-210156944,1484668,16],[1484668,64],[16]],[[0,0],[0]],[[-65476696,473916],[473916]],[[0,0],[0]],[[1654432,99956],[99956]],[[0,0],[0]],[[14098184,13316],[13316]],[[0,0],[0]],[[8350072,1004],[1004]],[[0,0],[0]],[[2880336,32],[32]],[[0]],[[662664]],[[0]],[[103096]],[[0]],[[10424]],[[0]],[[616]],[[0]],[[16]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
