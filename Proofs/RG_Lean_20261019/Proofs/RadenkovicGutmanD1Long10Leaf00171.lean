/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00171 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 171888950602975874065457217536000000000 1961613556225235715071205537988214784 4210321037654844579596206080000000000))
theorem leaf00171_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 171888950602975874065457217536000000000 1961613556225235715071205537988214784 4210321037654844579596206080000000000 raw00171=true := by decide +kernel
#print axioms leaf00171_raw
theorem leaf00171_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00171=true := by decide +kernel
#print axioms leaf00171_rectangular
def affine00171 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00171 (IntegerComputedClassCell.leftNumerator ![(19/800),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/800),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/800),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00171_transform : affine00171=(NestedInteger.clearedAll 3 raw00171 (IntegerComputedClassCell.leftNumerator ![(19/800),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/800),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/800),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00171_transform
theorem leaf00171_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00171=true := by decide +kernel
#print axioms leaf00171_sign
theorem leaf00171_log : RationalLog.accepts (8359095/1073741824) (-5213612293/2147483648) 8 8=true := by decide +kernel
#print axioms leaf00171_log
def leaf00171 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (18636237367/40000000000) (8359095/1073741824) (-5213612293/2147483648) 8 8 ![52,0,4] ![(19/800),0,0] ![(3/3200),1,(1/4)] affine00171
theorem leaf00171_checked : FastNestedCellData.accepts 1 0 4 leaf00171=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (18636237367/40000000000) (8359095/1073741824) (-5213612293/2147483648) 8 8 ![52,0,4] ![(19/800),0,0] ![(3/3200),1,(1/4)] 171888950602975874065457217536000000000 1961613556225235715071205537988214784 4210321037654844579596206080000000000 raw00171 affine00171
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00171_raw leaf00171_rectangular
    leaf00171_transform leaf00171_sign leaf00171_log
#print axioms leaf00171_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
