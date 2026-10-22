/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00386 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1742907898503832260547969024000000000 2052312371041508544037446363943796736 7240482242427473071238545408000000000))
theorem leaf00386_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1742907898503832260547969024000000000 2052312371041508544037446363943796736 7240482242427473071238545408000000000 raw00386=true := by decide +kernel
#print axioms leaf00386_raw
theorem leaf00386_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00386=true := by decide +kernel
#print axioms leaf00386_rectangular
def affine00386 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00386 (IntegerComputedClassCell.leftNumerator ![(37/80),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/80),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/80),0,(1/2)] ![(3/80),1,(1/2)]))
theorem leaf00386_transform : affine00386=(NestedInteger.clearedAll 3 raw00386 (IntegerComputedClassCell.leftNumerator ![(37/80),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/80),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/80),0,(1/2)] ![(3/80),1,(1/2)])) := by decide +kernel
#print axioms leaf00386_transform
theorem leaf00386_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00386=true := by decide +kernel
#print axioms leaf00386_sign
theorem leaf00386_log : RationalLog.accepts (1970244141/2147483648) (-184982765/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00386_log
def leaf00386 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (566899359/2000000000) (1970244141/2147483648) (-184982765/4294967296) 1 8 ![52,0,4] ![(37/80),0,(1/2)] ![(3/80),1,(1/2)] affine00386
theorem leaf00386_checked : FastNestedCellData.accepts 1 0 4 leaf00386=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (566899359/2000000000) (1970244141/2147483648) (-184982765/4294967296) 1 8 ![52,0,4] ![(37/80),0,(1/2)] ![(3/80),1,(1/2)] 1742907898503832260547969024000000000 2052312371041508544037446363943796736 7240482242427473071238545408000000000 raw00386 affine00386
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00386_raw leaf00386_rectangular
    leaf00386_transform leaf00386_sign leaf00386_log
#print axioms leaf00386_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
