/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00570 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 179252353335971907321649430528000000000000 2057701814196916683761695107025886773248 2520913888004399889261789184000000000000))
theorem leaf00570_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 179252353335971907321649430528000000000000 2057701814196916683761695107025886773248 2520913888004399889261789184000000000000 raw00570=true := by decide +kernel
#print axioms leaf00570_raw
theorem leaf00570_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00570=true := by decide +kernel
#print axioms leaf00570_rectangular
def affine00570 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00570 (IntegerComputedClassCell.leftNumerator ![(57/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(57/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(57/3200),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00570_transform : affine00570=(NestedInteger.clearedAll 3 raw00570 (IntegerComputedClassCell.leftNumerator ![(57/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(57/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(57/3200),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00570_transform
theorem leaf00570_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00570=true := by decide +kernel
#print axioms leaf00570_sign
theorem leaf00570_log : RationalLog.accepts (27145713/4294967296) (-1359351839/536870912) 8 8=true := by decide +kernel
#print axioms leaf00570_log
def leaf00570 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (408126160911/500000000000) (27145713/4294967296) (-1359351839/536870912) 8 8 ![60,0,4] ![(57/3200),0,0] ![(1/3200),1,(1/16)] affine00570
theorem leaf00570_checked : FastNestedCellData.accepts 1 2 4 leaf00570=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (408126160911/500000000000) (27145713/4294967296) (-1359351839/536870912) 8 8 ![60,0,4] ![(57/3200),0,0] ![(1/3200),1,(1/16)] 179252353335971907321649430528000000000000 2057701814196916683761695107025886773248 2520913888004399889261789184000000000000 raw00570 affine00570
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00570_raw leaf00570_rectangular
    leaf00570_transform leaf00570_sign leaf00570_log
#print axioms leaf00570_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
