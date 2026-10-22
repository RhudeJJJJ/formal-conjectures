/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00214 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 305239910838146402322500026368000000000000 293578135356985524576988143934219059462144 17741981098398291616931227107328000000000000))
theorem leaf00214_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 305239910838146402322500026368000000000000 293578135356985524576988143934219059462144 17741981098398291616931227107328000000000000 raw00214=true := by decide +kernel
#print axioms leaf00214_raw
theorem leaf00214_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00214=true := by decide +kernel
#print axioms leaf00214_rectangular
def affine00214 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00214 (IntegerComputedClassCell.leftNumerator ![(71/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(71/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(71/16000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00214_transform : affine00214=(NestedInteger.clearedAll 3 raw00214 (IntegerComputedClassCell.leftNumerator ![(71/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(71/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(71/16000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00214_transform
theorem leaf00214_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00214=true := by decide +kernel
#print axioms leaf00214_sign
theorem leaf00214_log : RationalLog.accepts (4063635541/4294967296) (-118897433/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00214_log
def leaf00214 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (16547088723/1000000000000) (4063635541/4294967296) (-118897433/4294967296) 1 8 ![60,0,4] ![(71/16000),0,(1/2)] ![(3/32000),1,(1/2)] affine00214
theorem leaf00214_checked : FastNestedCellData.accepts 1 2 4 leaf00214=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (16547088723/1000000000000) (4063635541/4294967296) (-118897433/4294967296) 1 8 ![60,0,4] ![(71/16000),0,(1/2)] ![(3/32000),1,(1/2)] 305239910838146402322500026368000000000000 293578135356985524576988143934219059462144 17741981098398291616931227107328000000000000 raw00214 affine00214
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00214_raw leaf00214_rectangular
    leaf00214_transform leaf00214_sign leaf00214_log
#print axioms leaf00214_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
