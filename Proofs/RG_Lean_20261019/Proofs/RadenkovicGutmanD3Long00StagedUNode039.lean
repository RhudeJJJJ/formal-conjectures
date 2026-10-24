/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode037
import Proofs.RadenkovicGutmanD3Long00StagedUNode038
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e039 : NestedArithmetic.Expr 3 := .plus e037 e038
noncomputable def p039 : NestedHorner.Poly 3 := [[[0],[0,-1]],[[0,0],[0]],[[45,-9],[-9]],[[0,0],[0]],[[309,-24],[-24]],[[0,0],[0]],[[893,-22],[-22]],[[0,0],[0]],[[1318,-8],[-8]],[[0,0],[0]],[[1020,-1],[-1]],[[0]],[[364]],[[0]],[[5]],[[0]],[[-38]],[[0]],[[-11]],[[0]],[[-1]]]
theorem step039 : p039=NestedHorner.add p037 p038 := by decide +kernel
#print axioms step039
theorem h039 : NestedArithmetic.compile e039=p039 := by
  change NestedHorner.add (NestedArithmetic.compile e037) (NestedArithmetic.compile e038)=p039
  rw [h037,h038]
  exact step039.symm
#print axioms h039
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
