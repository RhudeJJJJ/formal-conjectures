/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00175 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 17517533450620277706702454784000000000000 11852263293720713917755284638800883482624 65005009923876847146372169728000000000000))
theorem leaf00175_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 17517533450620277706702454784000000000000 11852263293720713917755284638800883482624 65005009923876847146372169728000000000000 raw00175=true := by decide +kernel
#print axioms leaf00175_raw
theorem leaf00175_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00175=true := by decide +kernel
#print axioms leaf00175_rectangular
def affine00175 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00175 (IntegerComputedClassCell.leftNumerator ![(79/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(79/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(79/3200),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00175_transform : affine00175=(NestedInteger.clearedAll 3 raw00175 (IntegerComputedClassCell.leftNumerator ![(79/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(79/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(79/3200),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00175_transform
theorem leaf00175_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00175=true := by decide +kernel
#print axioms leaf00175_sign
theorem leaf00175_log : RationalLog.accepts (1228909941/2147483648) (-1198659289/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00175_log
def leaf00175 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (45582114777/250000000000) (1228909941/2147483648) (-1198659289/4294967296) 1 8 ![52,0,4] ![(79/3200),0,(1/4)] ![(3/3200),1,(1/4)] affine00175
theorem leaf00175_checked : FastNestedCellData.accepts 1 0 4 leaf00175=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (45582114777/250000000000) (1228909941/2147483648) (-1198659289/4294967296) 1 8 ![52,0,4] ![(79/3200),0,(1/4)] ![(3/3200),1,(1/4)] 17517533450620277706702454784000000000000 11852263293720713917755284638800883482624 65005009923876847146372169728000000000000 raw00175 affine00175
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00175_raw leaf00175_rectangular
    leaf00175_transform leaf00175_sign leaf00175_log
#print axioms leaf00175_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
