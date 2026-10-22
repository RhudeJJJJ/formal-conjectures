/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00414 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 319798640086782949415003881472000000000000 416914669351598964220299835799266658353152 8016208995361554846348111511552000000000000))
theorem leaf00414_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 319798640086782949415003881472000000000000 416914669351598964220299835799266658353152 8016208995361554846348111511552000000000000 raw00414=true := by decide +kernel
#print axioms leaf00414_raw
theorem leaf00414_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00414=true := by decide +kernel
#print axioms leaf00414_rectangular
def affine00414 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00414 (IntegerComputedClassCell.leftNumerator ![(9/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/16),0,0] ![(1/16),1,(1/2)]))
theorem leaf00414_transform : affine00414=(NestedInteger.clearedAll 3 raw00414 (IntegerComputedClassCell.leftNumerator ![(9/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/16),0,0] ![(1/16),1,(1/2)])) := by decide +kernel
#print axioms leaf00414_transform
theorem leaf00414_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00414=true := by decide +kernel
#print axioms leaf00414_sign
theorem leaf00414_log : RationalLog.accepts (5322442611/4294967296) (460610319/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00414_log
def leaf00414 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (52008957051/1000000000000) (5322442611/4294967296) (460610319/4294967296) 0 8 ![52,0,4] ![(9/16),0,0] ![(1/16),1,(1/2)] affine00414
theorem leaf00414_checked : FastNestedCellData.accepts 1 0 4 leaf00414=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (52008957051/1000000000000) (5322442611/4294967296) (460610319/4294967296) 0 8 ![52,0,4] ![(9/16),0,0] ![(1/16),1,(1/2)] 319798640086782949415003881472000000000000 416914669351598964220299835799266658353152 8016208995361554846348111511552000000000000 raw00414 affine00414
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00414_raw leaf00414_rectangular
    leaf00414_transform leaf00414_sign leaf00414_log
#print axioms leaf00414_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
