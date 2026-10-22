/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00704 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 96638107216484870178169107251200000000000 77310443412972979352545590304391640907776 737869358652361589570440003584000000000000))
theorem leaf00704_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 96638107216484870178169107251200000000000 77310443412972979352545590304391640907776 737869358652361589570440003584000000000000 raw00704=true := by decide +kernel
#print axioms leaf00704_raw
theorem leaf00704_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00704=true := by decide +kernel
#print axioms leaf00704_rectangular
def affine00704 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00704 (IntegerComputedClassCell.leftNumerator ![(37/1280),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/1280),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/1280),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00704_transform : affine00704=(NestedInteger.clearedAll 3 raw00704 (IntegerComputedClassCell.leftNumerator ![(37/1280),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/1280),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/1280),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00704_transform
theorem leaf00704_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00704=true := by decide +kernel
#print axioms leaf00704_sign
theorem leaf00704_log : RationalLog.accepts (1555054735/2147483648) (-693177727/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00704_log
def leaf00704 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (104775245789/1000000000000) (1555054735/2147483648) (-693177727/4294967296) 1 8 ![60,0,4] ![(37/1280),0,(1/2)] ![(3/6400),1,(1/2)] affine00704
theorem leaf00704_checked : FastNestedCellData.accepts 1 2 4 leaf00704=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (104775245789/1000000000000) (1555054735/2147483648) (-693177727/4294967296) 1 8 ![60,0,4] ![(37/1280),0,(1/2)] ![(3/6400),1,(1/2)] 96638107216484870178169107251200000000000 77310443412972979352545590304391640907776 737869358652361589570440003584000000000000 raw00704 affine00704
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00704_raw leaf00704_rectangular
    leaf00704_transform leaf00704_sign leaf00704_log
#print axioms leaf00704_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
