/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode043
import Proofs.RadenkovicGutmanD26Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-6084],[0,-12168,3744],[-6084,3744]],[[0,0,0],[0,0,0],[0,0]],[[0,-240084,-19032],[-240084,18096,16224],[-19032,16224]],[[0,0,0],[0,0,0],[0,0]],[[-2232360,-1947348,56732],[-1947348,487864,19968],[56732,19968]],[[0,0,0],[0,0,0],[0,0]],[[-26942760,-5920668,341848],[-5920668,1655888,8736],[341848,8736]],[[0,0,0],[0,0,0],[0,0]],[[-143907192,-6723288,644592],[-6723288,2607072,1248],[644592,1248]],[[0,0,0],[0,0],[0]],[[-448375200,6049316,624728],[6049316,2282800],[624728]],[[0,0,0],[0,0],[0]],[[-898018784,31041452,343356],[31041452,1170936],[343356]],[[0,0,0],[0,0],[0]],[[-1184977040,48962992,107848],[48962992,349232],[107848]],[[0,0,0],[0,0],[0]],[[-972939864,45286020,18044],[45286020,56056],[18044]],[[0,0,0],[0,0],[0]],[[-325892632,27432652,1248],[27432652,3744],[1248]],[[0,0],[0]],[[298977536,11207352],[11207352]],[[0,0],[0]],[[540414680,3066700],[3066700]],[[0,0],[0]],[[434917912,539396],[539396]],[[0,0],[0]],[[228244848,55172],[55172]],[[0,0],[0]],[[84200064,2496],[2496]],[[0]],[[22139520]],[[0]],[[4080440]],[[0]],[[502216]],[[0]],[[37128]],[[0]],[[1248]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
