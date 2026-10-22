/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00143 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1168791598033299558105088000000000000 1003921254446017577712679001327140864 15110623238459194970472448000000000000))
theorem leaf00143_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1168791598033299558105088000000000000 1003921254446017577712679001327140864 15110623238459194970472448000000000000 raw00143=true := by decide +kernel
#print axioms leaf00143_raw
theorem leaf00143_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00143=true := by decide +kernel
#print axioms leaf00143_rectangular
def affine00143 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00143 (IntegerComputedClassCell.leftNumerator ![(29/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(29/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(29/1600),0,(1/2)] ![(1/1600),1,(1/2)]))
theorem leaf00143_transform : affine00143=(NestedInteger.clearedAll 3 raw00143 (IntegerComputedClassCell.leftNumerator ![(29/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(29/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(29/1600),0,(1/2)] ![(1/1600),1,(1/2)])) := by decide +kernel
#print axioms leaf00143_transform
theorem leaf00143_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00143=true := by decide +kernel
#print axioms leaf00143_sign
theorem leaf00143_log : RationalLog.accepts (108102763/134217728) (-232337383/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00143_log
def leaf00143 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (2076190949/31250000000) (108102763/134217728) (-232337383/2147483648) 1 8 ![52,0,4] ![(29/1600),0,(1/2)] ![(1/1600),1,(1/2)] affine00143
theorem leaf00143_checked : FastNestedCellData.accepts 1 0 4 leaf00143=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (2076190949/31250000000) (108102763/134217728) (-232337383/2147483648) 1 8 ![52,0,4] ![(29/1600),0,(1/2)] ![(1/1600),1,(1/2)] 1168791598033299558105088000000000000 1003921254446017577712679001327140864 15110623238459194970472448000000000000 raw00143 affine00143
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00143_raw leaf00143_rectangular
    leaf00143_transform leaf00143_sign leaf00143_log
#print axioms leaf00143_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
