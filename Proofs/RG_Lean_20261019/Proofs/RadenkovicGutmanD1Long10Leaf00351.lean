/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00351 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 176831579601048321854080548864000000000000 96531507425111952872027701992417757495296 157343573802848202650986479616000000000000))
theorem leaf00351_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 176831579601048321854080548864000000000000 96531507425111952872027701992417757495296 157343573802848202650986479616000000000000 raw00351=true := by decide +kernel
#print axioms leaf00351_raw
theorem leaf00351_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00351=true := by decide +kernel
#print axioms leaf00351_rectangular
def affine00351 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00351 (IntegerComputedClassCell.leftNumerator ![(7/40),0,0] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/40),0,0] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/40),0,0] ![(1/80),1,(1/4)]))
theorem leaf00351_transform : affine00351=(NestedInteger.clearedAll 3 raw00351 (IntegerComputedClassCell.leftNumerator ![(7/40),0,0] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/40),0,0] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/40),0,0] ![(1/80),1,(1/4)])) := by decide +kernel
#print axioms leaf00351_transform
theorem leaf00351_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00351=true := by decide +kernel
#print axioms leaf00351_sign
theorem leaf00351_log : RationalLog.accepts (1453108549/4294967296) (-2327311535/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00351_log
def leaf00351 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (76688473107/125000000000) (1453108549/4294967296) (-2327311535/4294967296) 2 8 ![52,0,4] ![(7/40),0,0] ![(1/80),1,(1/4)] affine00351
theorem leaf00351_checked : FastNestedCellData.accepts 1 0 4 leaf00351=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (76688473107/125000000000) (1453108549/4294967296) (-2327311535/4294967296) 2 8 ![52,0,4] ![(7/40),0,0] ![(1/80),1,(1/4)] 176831579601048321854080548864000000000000 96531507425111952872027701992417757495296 157343573802848202650986479616000000000000 raw00351 affine00351
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00351_raw leaf00351_rectangular
    leaf00351_transform leaf00351_sign leaf00351_log
#print axioms leaf00351_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
