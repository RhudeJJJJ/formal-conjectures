/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00072 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 702172368488939165915178598400000000000 423619200635754823359164301774422016 2318517542106983186615500800000000000))
theorem leaf00072_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 702172368488939165915178598400000000000 423619200635754823359164301774422016 2318517542106983186615500800000000000 raw00072=true := by decide +kernel
#print axioms leaf00072_raw
theorem leaf00072_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00072=true := by decide +kernel
#print axioms leaf00072_rectangular
def affine00072 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00072 (IntegerComputedClassCell.leftNumerator ![(1/128),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/128),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/128),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00072_transform : affine00072=(NestedInteger.clearedAll 3 raw00072 (IntegerComputedClassCell.leftNumerator ![(1/128),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/128),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/128),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00072_transform
theorem leaf00072_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00072=true := by decide +kernel
#print axioms leaf00072_sign
theorem leaf00072_log : RationalLog.accepts (547713/1073741824) (-16279877881/4294967296) 11 8=true := by decide +kernel
#print axioms leaf00072_log
def leaf00072 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (18271123377/100000000000) (547713/1073741824) (-16279877881/4294967296) 11 8 ![52,0,4] ![(1/128),0,0] ![(1/3200),1,(1/4)] affine00072
theorem leaf00072_checked : FastNestedCellData.accepts 1 0 4 leaf00072=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (18271123377/100000000000) (547713/1073741824) (-16279877881/4294967296) 11 8 ![52,0,4] ![(1/128),0,0] ![(1/3200),1,(1/4)] 702172368488939165915178598400000000000 423619200635754823359164301774422016 2318517542106983186615500800000000000 raw00072 affine00072
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00072_raw leaf00072_rectangular
    leaf00072_transform leaf00072_sign leaf00072_log
#print axioms leaf00072_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
