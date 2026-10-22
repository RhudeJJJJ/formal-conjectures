/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00396 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5401390016028856652589701267456000000000000 2843943025001158078127821376666103145562112 9712590460367795650841051922432000000000000))
theorem leaf00396_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5401390016028856652589701267456000000000000 2843943025001158078127821376666103145562112 9712590460367795650841051922432000000000000 raw00396=true := by decide +kernel
#print axioms leaf00396_raw
theorem leaf00396_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00396=true := by decide +kernel
#print axioms leaf00396_rectangular
def affine00396 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00396 (IntegerComputedClassCell.leftNumerator ![(63/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(63/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(63/6400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00396_transform : affine00396=(NestedInteger.clearedAll 3 raw00396 (IntegerComputedClassCell.leftNumerator ![(63/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(63/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(63/6400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00396_transform
theorem leaf00396_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00396=true := by decide +kernel
#print axioms leaf00396_sign
theorem leaf00396_log : RationalLog.accepts (1749204287/4294967296) (-1929048017/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00396_log
def leaf00396 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (292809939491/1000000000000) (1749204287/4294967296) (-1929048017/4294967296) 2 8 ![60,0,4] ![(63/6400),0,(1/16)] ![(1/6400),1,(1/16)] affine00396
theorem leaf00396_checked : FastNestedCellData.accepts 1 2 4 leaf00396=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (292809939491/1000000000000) (1749204287/4294967296) (-1929048017/4294967296) 2 8 ![60,0,4] ![(63/6400),0,(1/16)] ![(1/6400),1,(1/16)] 5401390016028856652589701267456000000000000 2843943025001158078127821376666103145562112 9712590460367795650841051922432000000000000 raw00396 affine00396
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00396_raw leaf00396_rectangular
    leaf00396_transform leaf00396_sign leaf00396_log
#print axioms leaf00396_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
