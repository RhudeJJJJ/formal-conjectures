/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00765 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 253799712411274448428710494208000000000000 12114499511458212792846595135926976905216 13757961811316124246383525888000000000000))
theorem leaf00765_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 253799712411274448428710494208000000000000 12114499511458212792846595135926976905216 13757961811316124246383525888000000000000 raw00765=true := by decide +kernel
#print axioms leaf00765_raw
theorem leaf00765_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00765=true := by decide +kernel
#print axioms leaf00765_rectangular
def affine00765 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00765 (IntegerComputedClassCell.leftNumerator ![(23/640),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/640),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/640),0,0] ![(3/3200),1,(1/16)]))
theorem leaf00765_transform : affine00765=(NestedInteger.clearedAll 3 raw00765 (IntegerComputedClassCell.leftNumerator ![(23/640),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/640),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/640),0,0] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00765_transform
theorem leaf00765_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00765=true := by decide +kernel
#print axioms leaf00765_sign
theorem leaf00765_log : RationalLog.accepts (109016081/4294967296) (-7889219085/4294967296) 6 8=true := by decide +kernel
#print axioms leaf00765_log
def leaf00765 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (110068079829/125000000000) (109016081/4294967296) (-7889219085/4294967296) 6 8 ![60,0,4] ![(23/640),0,0] ![(3/3200),1,(1/16)] affine00765
theorem leaf00765_checked : FastNestedCellData.accepts 1 2 4 leaf00765=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (110068079829/125000000000) (109016081/4294967296) (-7889219085/4294967296) 6 8 ![60,0,4] ![(23/640),0,0] ![(3/3200),1,(1/16)] 253799712411274448428710494208000000000000 12114499511458212792846595135926976905216 13757961811316124246383525888000000000000 raw00765 affine00765
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00765_raw leaf00765_rectangular
    leaf00765_transform leaf00765_sign leaf00765_log
#print axioms leaf00765_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
