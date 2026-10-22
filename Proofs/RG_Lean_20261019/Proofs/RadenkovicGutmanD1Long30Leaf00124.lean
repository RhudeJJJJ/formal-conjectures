/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00124 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1700452048323717055532498944000000000000 1658895556525543431000310678228507295744 160677976600435207882479239168000000000000))
theorem leaf00124_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1700452048323717055532498944000000000000 1658895556525543431000310678228507295744 160677976600435207882479239168000000000000 raw00124=true := by decide +kernel
#print axioms leaf00124_raw
theorem leaf00124_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00124=true := by decide +kernel
#print axioms leaf00124_rectangular
def affine00124 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00124 (IntegerComputedClassCell.leftNumerator ![(11/4000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/4000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/4000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00124_transform : affine00124=(NestedInteger.clearedAll 3 raw00124 (IntegerComputedClassCell.leftNumerator ![(11/4000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/4000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/4000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00124_transform
theorem leaf00124_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00124=true := by decide +kernel
#print axioms leaf00124_sign
theorem leaf00124_log : RationalLog.accepts (4147187737/4294967296) (-37595467/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00124_log
def leaf00124 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (2581087327/250000000000) (4147187737/4294967296) (-37595467/2147483648) 1 8 ![60,0,4] ![(11/4000),0,(1/2)] ![(3/32000),1,(1/2)] affine00124
theorem leaf00124_checked : FastNestedCellData.accepts 1 2 4 leaf00124=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (2581087327/250000000000) (4147187737/4294967296) (-37595467/2147483648) 1 8 ![60,0,4] ![(11/4000),0,(1/2)] ![(3/32000),1,(1/2)] 1700452048323717055532498944000000000000 1658895556525543431000310678228507295744 160677976600435207882479239168000000000000 raw00124 affine00124
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00124_raw leaf00124_rectangular
    leaf00124_transform leaf00124_sign leaf00124_log
#print axioms leaf00124_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
