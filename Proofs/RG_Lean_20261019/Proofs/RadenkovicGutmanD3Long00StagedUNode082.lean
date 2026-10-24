/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode079
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e082 : NestedArithmetic.Expr 3 := .scaled -1 e079
noncomputable def p082 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,486,0],[486,81,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[8019,7047,0],[7047,702,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[130977,43416,0],[43416,2385,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[951588,150435,0],[150435,4122,0],[0,0]],[[0,0,0],[0,0],[0]],[[4088205,327888,0],[327888,3996],[0]],[[0,0,0],[0,0],[0]],[[11656161,477153,0],[477153,2250],[0]],[[0,0,0],[0,0],[0]],[[23469966,479844,0],[479844,729],[0]],[[0,0,0],[0,0],[0]],[[34660044,339732,0],[339732,126],[0]],[[0,0,0],[0,0],[0]],[[38456451,170370,0],[170370,9],[0]],[[0,0],[0]],[[32545206,60111],[60111]],[[0,0],[0]],[[21183930,14580],[14580]],[[0,0],[0]],[[10632312,2313],[2313]],[[0,0],[0]],[[4101363,216],[216]],[[0,0],[0]],[[1203813,9],[9]],[[0]],[[263790]],[[0]],[[41760]],[[0]],[[4509]],[[0]],[[297]],[[0]],[[9]]]
theorem step082 : p082=NestedHorner.scale -1 p079 := by decide +kernel
#print axioms step082
theorem h082 : NestedArithmetic.compile e082=p082 := by
  change NestedHorner.scale -1 (NestedArithmetic.compile e079)=p082
  rw [h079]
  exact step082.symm
#print axioms h082
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
