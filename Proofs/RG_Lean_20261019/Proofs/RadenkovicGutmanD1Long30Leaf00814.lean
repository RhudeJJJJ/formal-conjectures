/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00814 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 574486485390553399542099948339200000000000 421632460701015732559642555203064602558464 2707721171345741524665047711744000000000000))
theorem leaf00814_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 574486485390553399542099948339200000000000 421632460701015732559642555203064602558464 2707721171345741524665047711744000000000000 raw00814=true := by decide +kernel
#print axioms leaf00814_raw
theorem leaf00814_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00814=true := by decide +kernel
#print axioms leaf00814_rectangular
def affine00814 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00814 (IntegerComputedClassCell.leftNumerator ![(71/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(71/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(71/1600),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00814_transform : affine00814=(NestedInteger.clearedAll 3 raw00814 (IntegerComputedClassCell.leftNumerator ![(71/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(71/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(71/1600),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00814_transform
theorem leaf00814_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00814=true := by decide +kernel
#print axioms leaf00814_sign
theorem leaf00814_log : RationalLog.accepts (2727491345/4294967296) (-975090059/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00814_log
def leaf00814 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (155714873881/1000000000000) (2727491345/4294967296) (-975090059/4294967296) 1 8 ![60,0,4] ![(71/1600),0,(1/2)] ![(3/3200),1,(1/2)] affine00814
theorem leaf00814_checked : FastNestedCellData.accepts 1 2 4 leaf00814=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (155714873881/1000000000000) (2727491345/4294967296) (-975090059/4294967296) 1 8 ![60,0,4] ![(71/1600),0,(1/2)] ![(3/3200),1,(1/2)] 574486485390553399542099948339200000000000 421632460701015732559642555203064602558464 2707721171345741524665047711744000000000000 raw00814 affine00814
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00814_raw leaf00814_rectangular
    leaf00814_transform leaf00814_sign leaf00814_log
#print axioms leaf00814_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
