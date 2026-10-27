/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023AffineLength
import Proofs.RadenkovicGutmanPowerBernstein
namespace Gebendorfer.RadenkovicGutman.D5UpperPowerSquareCell0023
open D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem leaf00023_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] leaf00023_w_affine=true :=
  PowerBernstein.checked 3 ![88,4,4] leaf00023_w_affine
    (by decide +kernel) (by decide +kernel)
#print axioms leaf00023_sign
theorem leaf00023_log : RationalLog.accepts (399917283518884009/2361183241434822606848) (-5125783901601593430591/1180591620717411303424) 13 32=true := by decide +kernel
#print axioms leaf00023_log
noncomputable def leaf00023 : FastNestedCellData.Cell := IntegerScaledCell.make FixedDegree05Long00CompositionalNormPack.pack false (5755267077/250000000000) (399917283518884009/2361183241434822606848) (-5125783901601593430591/1180591620717411303424) 13 32 ![88,4,4] ![(27/3200),0,0] ![(1/3200),1,1] 3397310043048494197631902285824000000000000 ![3200,1,1] leaf00023_w_affine
theorem leaf00023_checked : FastNestedCellData.accepts 5 4 4 leaf00023=true :=
  IntegerPiecewiseCell.accepts_make FixedDegree05Long00CompositionalIntegerNorm.pack false (5755267077/250000000000) (399917283518884009/2361183241434822606848) (-5125783901601593430591/1180591620717411303424) 13 32 ![88,4,4] ![(27/3200),0,0] ![(1/3200),1,1]
    3397310043048494197631902285824000000000000 588654193664713519532850443010176351361 25570237913770127523694867923250000000000 ![27,0,0] ![1,1,1] ![3200,1,1] leaf00023_w_raw leaf00023_w_inner leaf00023_w_affine
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    leaf00023_raw leaf00023_rectangular leaf00023_inner leaf00023_w_affine_eval leaf00023_sign leaf00023_log
#print axioms leaf00023_checked
end Gebendorfer.RadenkovicGutman.D5UpperPowerSquareCell0023
