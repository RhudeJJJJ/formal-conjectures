/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00965 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3523234818841936311305226944512000000000000 1148313318501975511109036909012532177403904 1503067705674572245480157216768000000000000))
theorem leaf00965_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3523234818841936311305226944512000000000000 1148313318501975511109036909012532177403904 1503067705674572245480157216768000000000000 raw00965=true := by decide +kernel
#print axioms leaf00965_raw
theorem leaf00965_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00965=true := by decide +kernel
#print axioms leaf00965_rectangular
def affine00965 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00965 (IntegerComputedClassCell.leftNumerator ![(17/160),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/160),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/160),0,0] ![(1/160),1,(1/16)]))
theorem leaf00965_transform : affine00965=(NestedInteger.clearedAll 3 raw00965 (IntegerComputedClassCell.leftNumerator ![(17/160),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/160),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/160),0,0] ![(1/160),1,(1/16)])) := by decide +kernel
#print axioms leaf00965_transform
theorem leaf00965_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00965=true := by decide +kernel
#print axioms leaf00965_sign
theorem leaf00965_log : RationalLog.accepts (396784847/2147483648) (-226647827/268435456) 3 8=true := by decide +kernel
#print axioms leaf00965_log
def leaf00965 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (763979768953/1000000000000) (396784847/2147483648) (-226647827/268435456) 3 8 ![60,0,4] ![(17/160),0,0] ![(1/160),1,(1/16)] affine00965
theorem leaf00965_checked : FastNestedCellData.accepts 1 2 4 leaf00965=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (763979768953/1000000000000) (396784847/2147483648) (-226647827/268435456) 3 8 ![60,0,4] ![(17/160),0,0] ![(1/160),1,(1/16)] 3523234818841936311305226944512000000000000 1148313318501975511109036909012532177403904 1503067705674572245480157216768000000000000 raw00965 affine00965
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00965_raw leaf00965_rectangular
    leaf00965_transform leaf00965_sign leaf00965_log
#print axioms leaf00965_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
