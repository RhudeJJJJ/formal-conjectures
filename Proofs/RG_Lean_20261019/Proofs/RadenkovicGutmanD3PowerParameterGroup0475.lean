/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0475AffineLength
import Proofs.RadenkovicGutmanPowerBernstein
namespace Gebendorfer.RadenkovicGutman.D3PowerParameterGroup0475
open D3FullParameterGroup0475
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem leaf01900_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] leaf01900_w_affine=true :=
  PowerBernstein.checked 3 ![88,4,4] leaf01900_w_affine
    (by decide +kernel) (by decide +kernel)
#print axioms leaf01900_sign
theorem leaf01900_log : RationalLog.accepts (123659149971711449441/4722366482869645213696) (-8600695753426310452355/4722366482869645213696) 6 32=true := by decide +kernel
#print axioms leaf01900_log
noncomputable def leaf01900 : FastNestedCellData.Cell := IntegerScaledCell.make FixedDegree03Long00StagedNormPack.pack false (56165509097/250000000000) (123659149971711449441/4722366482869645213696) (-8600695753426310452355/4722366482869645213696) 6 32 ![88,4,4] ![(559/12800),0,0] ![(3/12800),1,1] 66308529413245738228751299248128000000000000 ![12800,1,1] leaf01900_w_affine
theorem leaf01900_checked : FastNestedCellData.accepts 3 4 4 leaf01900=true :=
  IntegerPiecewiseCell.accepts_make FixedDegree03Long00StagedIntegerNorm.pack false (56165509097/250000000000) (123659149971711449441/4722366482869645213696) (-8600695753426310452355/4722366482869645213696) 6 32 ![88,4,4] ![(559/12800),0,0] ![(3/12800),1,1]
    66308529413245738228751299248128000000000000 2126435531900274280437944565510893659776369 9465041651397827266621885266194250000000000 ![559,0,0] ![3,1,1] ![12800,1,1] leaf01900_w_raw leaf01900_w_inner leaf01900_w_affine
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    leaf01900_raw leaf01900_rectangular leaf01900_inner leaf01900_w_affine_eval leaf01900_sign leaf01900_log
#print axioms leaf01900_checked
end Gebendorfer.RadenkovicGutman.D3PowerParameterGroup0475
