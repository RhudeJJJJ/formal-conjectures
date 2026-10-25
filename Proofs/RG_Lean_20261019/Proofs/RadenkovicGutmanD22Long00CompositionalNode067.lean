/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode043
import Proofs.RadenkovicGutmanD22Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,4356],[0,8712,-5280],[4356,-5280,1600]],[[0,0,0],[0,0,0],[0,0]],[[0,148500,-9768],[148500,-109536,5920],[-9768,5920]],[[0,0,0],[0,0,0],[0,0]],[[1020600,431460,-74780],[431460,-511960,48640],[-74780,48640]],[[0,0,0],[0,0,0],[0,0]],[[5945400,-1532484,-5848],[-1532484,-318336,58080],[-5848,58080]],[[0,0,0],[0,0,0],[0,0]],[[-3688200,-8867960,437776],[-8867960,1577792,23840],[437776,23840]],[[0,0,0],[0,0,0],[0,0]],[[-135015120,-13662212,921640],[-13662212,3693200,3200],[921640,3200]],[[0,0,0],[0,0],[0]],[[-569602416,2684676,895364],[2684676,3643048],[895364]],[[0,0,0],[0,0],[0]],[[-1286316688,40003472,481336],[40003472,1957152],[481336]],[[0,0,0],[0,0],[0]],[[-1806724840,68000092,146884],[68000092,594408],[146884]],[[0,0,0],[0,0],[0]],[[-1562692280,63696436,23840],[63696436,95920],[23840]],[[0,0,0],[0,0],[0]],[[-615074976,38353208,1600],[38353208,6400],[1600]],[[0,0],[0]],[[335792520,15456980],[15456980]],[[0,0],[0]],[[724966504,4158444],[4158444]],[[0,0],[0]],[[596844160,718108],[718108]],[[0,0],[0]],[[313436784,72080],[72080]],[[0,0],[0]],[[114831840,3200],[3200]],[[0]],[[29883720]],[[0]],[[5441928]],[[0]],[[661224]],[[0]],[[48240]],[[0]],[[1600]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
