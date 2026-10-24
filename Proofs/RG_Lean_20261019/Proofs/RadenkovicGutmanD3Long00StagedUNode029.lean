/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode023
import Proofs.RadenkovicGutmanD3Long00StagedUNode026
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e029 : NestedArithmetic.Expr 3 := .times e023 e026
noncomputable def p029 : NestedHorner.Poly 3 := [[[],[0,1]],[[0,0],[0]],[[0,9],[9]],[[0,0],[0]],[[81,24],[24]],[[0,0],[0]],[[432,22],[22]],[[0,0],[0]],[[972,8],[8]],[[0,0],[0]],[[1200,1],[1]],[[0]],[[886]],[[0]],[[400]],[[0]],[[108]],[[0]],[[16]],[[0]],[[1]]]
theorem step029 : p029=NestedArithmetic.mul p023 p026 := by decide +kernel
#print axioms step029
theorem h029 : NestedArithmetic.compile e029=p029 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e023) (NestedArithmetic.compile e026)=p029
  rw [h023,h026]
  exact step029.symm
#print axioms h029
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
