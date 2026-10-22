/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00907 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 167703841003930438162330943488000000000000 65451269792701064869160626480853649719296 112490232775975956127990939648000000000000))
theorem leaf00907_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 167703841003930438162330943488000000000000 65451269792701064869160626480853649719296 112490232775975956127990939648000000000000 raw00907=true := by decide +kernel
#print axioms leaf00907_raw
theorem leaf00907_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00907=true := by decide +kernel
#print axioms leaf00907_rectangular
def affine00907 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00907 (IntegerComputedClassCell.leftNumerator ![(9/128),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(9/128),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(9/128),0,(1/8)] ![(1/640),1,(1/8)]))
theorem leaf00907_transform : affine00907=(NestedInteger.clearedAll 3 raw00907 (IntegerComputedClassCell.leftNumerator ![(9/128),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(9/128),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(9/128),0,(1/8)] ![(1/640),1,(1/8)])) := by decide +kernel
#print axioms leaf00907_transform
theorem leaf00907_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00907=true := by decide +kernel
#print axioms leaf00907_sign
theorem leaf00907_log : RationalLog.accepts (264918629/1073741824) (-23479415/33554432) 3 8=true := by decide +kernel
#print axioms leaf00907_log
def leaf00907 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (290919790001/500000000000) (264918629/1073741824) (-23479415/33554432) 3 8 ![60,0,4] ![(9/128),0,(1/8)] ![(1/640),1,(1/8)] affine00907
theorem leaf00907_checked : FastNestedCellData.accepts 1 2 4 leaf00907=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (290919790001/500000000000) (264918629/1073741824) (-23479415/33554432) 3 8 ![60,0,4] ![(9/128),0,(1/8)] ![(1/640),1,(1/8)] 167703841003930438162330943488000000000000 65451269792701064869160626480853649719296 112490232775975956127990939648000000000000 raw00907 affine00907
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00907_raw leaf00907_rectangular
    leaf00907_transform leaf00907_sign leaf00907_log
#print axioms leaf00907_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
