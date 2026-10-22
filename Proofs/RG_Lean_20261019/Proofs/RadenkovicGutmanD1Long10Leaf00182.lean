/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00182 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 277870685740604244050753617920000000000 224617795822977246029861434658396307456 2329920898560068976788897792000000000000))
theorem leaf00182_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 277870685740604244050753617920000000000 224617795822977246029861434658396307456 2329920898560068976788897792000000000000 raw00182=true := by decide +kernel
#print axioms leaf00182_raw
theorem leaf00182_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00182=true := by decide +kernel
#print axioms leaf00182_rectangular
def affine00182 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00182 (IntegerComputedClassCell.leftNumerator ![(17/640),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/640),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/640),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00182_transform : affine00182=(NestedInteger.clearedAll 3 raw00182 (IntegerComputedClassCell.leftNumerator ![(17/640),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/640),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/640),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00182_transform
theorem leaf00182_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00182=true := by decide +kernel
#print axioms leaf00182_sign
theorem leaf00182_log : RationalLog.accepts (3166576475/4294967296) (-81817229/536870912) 1 8=true := by decide +kernel
#print axioms leaf00182_log
def leaf00182 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (6025360023/62500000000) (3166576475/4294967296) (-81817229/536870912) 1 8 ![52,0,4] ![(17/640),0,(1/2)] ![(3/3200),1,(1/2)] affine00182
theorem leaf00182_checked : FastNestedCellData.accepts 1 0 4 leaf00182=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (6025360023/62500000000) (3166576475/4294967296) (-81817229/536870912) 1 8 ![52,0,4] ![(17/640),0,(1/2)] ![(3/3200),1,(1/2)] 277870685740604244050753617920000000000 224617795822977246029861434658396307456 2329920898560068976788897792000000000000 raw00182 affine00182
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00182_raw leaf00182_rectangular
    leaf00182_transform leaf00182_sign leaf00182_log
#print axioms leaf00182_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
