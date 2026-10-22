/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00867 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 31911725462773483349003049369600000000000 12189568328406099889773806493648398843904 22019516735452188905478029312000000000000))
theorem leaf00867_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 31911725462773483349003049369600000000000 12189568328406099889773806493648398843904 22019516735452188905478029312000000000000 raw00867=true := by decide +kernel
#print axioms leaf00867_raw
theorem leaf00867_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00867=true := by decide +kernel
#print axioms leaf00867_rectangular
def affine00867 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00867 (IntegerComputedClassCell.leftNumerator ![(37/640),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(37/640),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(37/640),0,(1/8)] ![(1/640),1,(1/8)]))
theorem leaf00867_transform : affine00867=(NestedInteger.clearedAll 3 raw00867 (IntegerComputedClassCell.leftNumerator ![(37/640),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(37/640),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(37/640),0,(1/8)] ![(1/640),1,(1/8)])) := by decide +kernel
#print axioms leaf00867_transform
theorem leaf00867_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00867=true := by decide +kernel
#print axioms leaf00867_sign
theorem leaf00867_log : RationalLog.accepts (1056000745/4294967296) (-3012823137/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00867_log
def leaf00867 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (69197524149/125000000000) (1056000745/4294967296) (-3012823137/4294967296) 3 8 ![60,0,4] ![(37/640),0,(1/8)] ![(1/640),1,(1/8)] affine00867
theorem leaf00867_checked : FastNestedCellData.accepts 1 2 4 leaf00867=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (69197524149/125000000000) (1056000745/4294967296) (-3012823137/4294967296) 3 8 ![60,0,4] ![(37/640),0,(1/8)] ![(1/640),1,(1/8)] 31911725462773483349003049369600000000000 12189568328406099889773806493648398843904 22019516735452188905478029312000000000000 raw00867 affine00867
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00867_raw leaf00867_rectangular
    leaf00867_transform leaf00867_sign leaf00867_log
#print axioms leaf00867_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
