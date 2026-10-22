/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00172 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 793033623327406191137521664000000000000 542585511347396461400206070639090466816 3081316901127056629614772224000000000000))
theorem leaf00172_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 793033623327406191137521664000000000000 542585511347396461400206070639090466816 3081316901127056629614772224000000000000 raw00172=true := by decide +kernel
#print axioms leaf00172_raw
theorem leaf00172_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00172=true := by decide +kernel
#print axioms leaf00172_rectangular
def affine00172 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00172 (IntegerComputedClassCell.leftNumerator ![(19/800),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/800),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/800),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00172_transform : affine00172=(NestedInteger.clearedAll 3 raw00172 (IntegerComputedClassCell.leftNumerator ![(19/800),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/800),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/800),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00172_transform
theorem leaf00172_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00172=true := by decide +kernel
#print axioms leaf00172_sign
theorem leaf00172_log : RationalLog.accepts (624649409/1073741824) (-1163322663/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00172_log
def leaf00172 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (11005552349/62500000000) (624649409/1073741824) (-1163322663/4294967296) 1 8 ![52,0,4] ![(19/800),0,(1/4)] ![(3/3200),1,(1/4)] affine00172
theorem leaf00172_checked : FastNestedCellData.accepts 1 0 4 leaf00172=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (11005552349/62500000000) (624649409/1073741824) (-1163322663/4294967296) 1 8 ![52,0,4] ![(19/800),0,(1/4)] ![(3/3200),1,(1/4)] 793033623327406191137521664000000000000 542585511347396461400206070639090466816 3081316901127056629614772224000000000000 raw00172 affine00172
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00172_raw leaf00172_rectangular
    leaf00172_transform leaf00172_sign leaf00172_log
#print axioms leaf00172_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
