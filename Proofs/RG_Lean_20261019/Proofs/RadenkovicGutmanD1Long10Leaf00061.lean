/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00061 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 14628664128564131581518675968000000000000 12975437857353691721104860809615175057408 255656654735520580495699083264000000000000))
theorem leaf00061_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 14628664128564131581518675968000000000000 12975437857353691721104860809615175057408 255656654735520580495699083264000000000000 raw00061=true := by decide +kernel
#print axioms leaf00061_raw
theorem leaf00061_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00061=true := by decide +kernel
#print axioms leaf00061_rectangular
def affine00061 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00061 (IntegerComputedClassCell.leftNumerator ![(21/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/3200),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00061_transform : affine00061=(NestedInteger.clearedAll 3 raw00061 (IntegerComputedClassCell.leftNumerator ![(21/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/3200),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00061_transform
theorem leaf00061_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00061=true := by decide +kernel
#print axioms leaf00061_sign
theorem leaf00061_log : RationalLog.accepts (1812785529/2147483648) (-11370399/134217728) 1 8=true := by decide +kernel
#print axioms leaf00061_log
def leaf00061 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (12688343543/250000000000) (1812785529/2147483648) (-11370399/134217728) 1 8 ![52,0,4] ![(21/3200),0,(1/4)] ![(1/3200),1,(1/4)] affine00061
theorem leaf00061_checked : FastNestedCellData.accepts 1 0 4 leaf00061=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (12688343543/250000000000) (1812785529/2147483648) (-11370399/134217728) 1 8 ![52,0,4] ![(21/3200),0,(1/4)] ![(1/3200),1,(1/4)] 14628664128564131581518675968000000000000 12975437857353691721104860809615175057408 255656654735520580495699083264000000000000 raw00061 affine00061
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00061_raw leaf00061_rectangular
    leaf00061_transform leaf00061_sign leaf00061_log
#print axioms leaf00061_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
