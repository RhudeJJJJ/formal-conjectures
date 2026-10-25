/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode033
import Proofs.RadenkovicGutmanD33Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1089]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,26136],[0,26136,66]],[[0,0,0],[0,0,0],[0,0]],[[-88209,-58806,147015],[-58806,568458,81774],[147015,81774]],[[0,0,0],[0,0,0],[0,0]],[[-2416392,2234628,887436],[2234628,3379860,85932],[887436,85932]],[[0,0,0],[0,0,0],[0,0]],[[-10354311,21893652,2223936],[21893652,8318574,35574],[2223936,35574]],[[0,0,0],[0,0,0],[0,0]],[[24990174,87447690,3019698],[87447690,11081268,5412],[3019698,5412]],[[0,0,0],[0,0,0],[0,0]],[[356958261,201117708,2429262],[201117708,8750016,132],[2429262,132]],[[0,0,0],[0,0],[0]],[[1478366736,300323628,1188858],[300323628,4210932],[1188858]],[[0,0,0],[0,0],[0]],[[3643152810,308023848,348744],[308023848,1218558],[348744]],[[0,0,0],[0,0],[0]],[[6164894472,222960474,57222],[222960474,198396],[57222]],[[0,0,0],[0,0],[0]],[[7602314610,114984870,4323],[114984870,15114],[4323]],[[0,0,0],[0,0],[0]],[[7041295140,42049458,66],[42049458,264],[66]],[[0,0],[0]],[[4975686672,10684080],[10684080]],[[0,0],[0]],[[2700019608,1806420],[1806420]],[[0,0],[0]],[[1124263569,186516],[186516]],[[0,0],[0]],[[356402376,9702],[9702]],[[0,0],[0]],[[84617874,132],[132]],[[0]],[[14623488]],[[0]],[[1752465]],[[0]],[[133452]],[[0]],[[5379]],[[0]],[[66]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
