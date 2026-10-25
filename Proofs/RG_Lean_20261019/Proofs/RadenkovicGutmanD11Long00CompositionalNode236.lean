/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode235
import Proofs.RadenkovicGutmanD11Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e236 : NestedArithmetic.Expr 3 := .times e235 e122
noncomputable def p236 : NestedHorner.Poly 3 := [[[121],[0],[0]],[[0,0],[0,0],[0]],[[3751,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[53361,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[461736,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2715966,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[11496573,242,0],[242,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[36165085,5566,0],[5566,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[86083272,57112,0],[57112,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[156361524,344850,0],[344850,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[216868300,1361250,0],[1361250,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[227997275,3691347,121],[3691347,363,0],[121,0]],[[0,0,0],[0,0,0],[0,0]],[[178516140,7033609,1815],[7033609,5566,0],[1815,0]],[[0,0,0],[0,0,0],[0,0]],[[100571570,9463894,11374],[9463894,35695,0],[11374,0]],[[0,0,0],[0,0,0],[0,0]],[[37997509,8894831,38599],[8894831,124146,0],[38599,0]],[[0,0,0],[0,0,0],[0,0]],[[7993623,5662074,76956],[5662074,254100,0],[76956,0]],[[0,0,0],[0,0,0],[0,0]],[[169884,2286779,91597],[2286779,310970,121],[91597,121]],[[0,0,0],[0,0,0],[0,0]],[[-310365,505296,63162],[505296,220583,847],[63162,847]],[[0,0,0],[0,0,0],[0,0]],[[-49005,35937,22869],[35937,82038,1936],[22869,1936]],[[0,0,0],[0,0,0],[0,0]],[[0,-3267,3267],[-3267,11979,1573],[3267,1573]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,363],[0,363]]]
theorem step236 : p236=NestedArithmetic.mul p235 p122 := by decide +kernel
#print axioms step236
theorem h236 : NestedArithmetic.compile e236=p236 := StagedExprCompile.compile_times e236 e235 e122 p235 p122 p236 rfl h235 h122 step236
#print axioms h236
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
