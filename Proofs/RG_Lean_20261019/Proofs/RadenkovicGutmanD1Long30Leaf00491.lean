/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00491 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6766933748122599832470918529024000000000000 3037461466159194968211153532264229388681216 8280157067525365356486715244544000000000000))
theorem leaf00491_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6766933748122599832470918529024000000000000 3037461466159194968211153532264229388681216 8280157067525365356486715244544000000000000 raw00491=true := by decide +kernel
#print axioms leaf00491_raw
theorem leaf00491_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00491=true := by decide +kernel
#print axioms leaf00491_rectangular
def affine00491 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00491 (IntegerComputedClassCell.leftNumerator ![(41/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/3200),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00491_transform : affine00491=(NestedInteger.clearedAll 3 raw00491 (IntegerComputedClassCell.leftNumerator ![(41/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/3200),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00491_transform
theorem leaf00491_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00491=true := by decide +kernel
#print axioms leaf00491_sign
theorem leaf00491_log : RationalLog.accepts (1410464751/4294967296) (-2391276113/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00491_log
def leaf00491 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (366836213539/1000000000000) (1410464751/4294967296) (-2391276113/4294967296) 2 8 ![60,0,4] ![(41/3200),0,(1/16)] ![(1/3200),1,(1/16)] affine00491
theorem leaf00491_checked : FastNestedCellData.accepts 1 2 4 leaf00491=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (366836213539/1000000000000) (1410464751/4294967296) (-2391276113/4294967296) 2 8 ![60,0,4] ![(41/3200),0,(1/16)] ![(1/3200),1,(1/16)] 6766933748122599832470918529024000000000000 3037461466159194968211153532264229388681216 8280157067525365356486715244544000000000000 raw00491 affine00491
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00491_raw leaf00491_rectangular
    leaf00491_transform leaf00491_sign leaf00491_log
#print axioms leaf00491_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
