/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode033
import Proofs.RadenkovicGutmanD11Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,363],[0,363]],[[0,0,0],[0,0,0],[0,0]],[[0,-3267,3267],[-3267,11979,1573],[3267,1573]],[[0,0,0],[0,0,0],[0,0]],[[-49005,35937,22869],[35937,82038,1936],[22869,1936]],[[0,0,0],[0,0,0],[0,0]],[[-310365,505296,63162],[505296,220583,847],[63162,847]],[[0,0,0],[0,0,0],[0,0]],[[169884,2286779,91597],[2286779,310970,121],[91597,121]],[[0,0,0],[0,0],[0]],[[7993623,5662074,76956],[5662074,254100],[76956]],[[0,0,0],[0,0],[0]],[[37997509,8894831,38599],[8894831,124146],[38599]],[[0,0,0],[0,0],[0]],[[100571570,9463894,11374],[9463894,35695],[11374]],[[0,0,0],[0,0],[0]],[[178516140,7033609,1815],[7033609,5566],[1815]],[[0,0,0],[0,0],[0]],[[227997275,3691347,121],[3691347,363],[121]],[[0,0],[0]],[[216868300,1361250],[1361250]],[[0,0],[0]],[[156361524,344850],[344850]],[[0,0],[0]],[[86083272,57112],[57112]],[[0,0],[0]],[[36165085,5566],[5566]],[[0,0],[0]],[[11496573,242],[242]],[[0]],[[2715966]],[[0]],[[461736]],[[0]],[[53361]],[[0]],[[3751]],[[0]],[[121]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
