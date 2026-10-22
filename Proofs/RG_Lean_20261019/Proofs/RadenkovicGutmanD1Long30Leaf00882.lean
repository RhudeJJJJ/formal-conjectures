/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00882 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 34819698672486040641970425036800000000000 13365339733613463223825498829642193174528 23602253027629479858338476851200000000000))
theorem leaf00882_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 34819698672486040641970425036800000000000 13365339733613463223825498829642193174528 23602253027629479858338476851200000000000 raw00882=true := by decide +kernel
#print axioms leaf00882_raw
theorem leaf00882_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00882=true := by decide +kernel
#print axioms leaf00882_rectangular
def affine00882 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00882 (IntegerComputedClassCell.leftNumerator ![(1/16),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/16),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/16),0,(1/8)] ![(1/640),1,(1/8)]))
theorem leaf00882_transform : affine00882=(NestedInteger.clearedAll 3 raw00882 (IntegerComputedClassCell.leftNumerator ![(1/16),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/16),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/16),0,(1/8)] ![(1/640),1,(1/8)])) := by decide +kernel
#print axioms leaf00882_transform
theorem leaf00882_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00882=true := by decide +kernel
#print axioms leaf00882_sign
theorem leaf00882_log : RationalLog.accepts (1052560689/4294967296) (-188739391/268435456) 3 8=true := by decide +kernel
#print axioms leaf00882_log
def leaf00882 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (56627389419/100000000000) (1052560689/4294967296) (-188739391/268435456) 3 8 ![60,0,4] ![(1/16),0,(1/8)] ![(1/640),1,(1/8)] affine00882
theorem leaf00882_checked : FastNestedCellData.accepts 1 2 4 leaf00882=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (56627389419/100000000000) (1052560689/4294967296) (-188739391/268435456) 3 8 ![60,0,4] ![(1/16),0,(1/8)] ![(1/640),1,(1/8)] 34819698672486040641970425036800000000000 13365339733613463223825498829642193174528 23602253027629479858338476851200000000000 raw00882 affine00882
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00882_raw leaf00882_rectangular
    leaf00882_transform leaf00882_sign leaf00882_log
#print axioms leaf00882_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
