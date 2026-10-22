/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00077 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 108295747976037474838668902400000000000 100786607746576448912966698788741709824 3353058915604721538399469568000000000000))
theorem leaf00077_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 108295747976037474838668902400000000000 100786607746576448912966698788741709824 3353058915604721538399469568000000000000 raw00077=true := by decide +kernel
#print axioms leaf00077_raw
theorem leaf00077_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00077=true := by decide +kernel
#print axioms leaf00077_rectangular
def affine00077 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00077 (IntegerComputedClassCell.leftNumerator ![(13/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/1600),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00077_transform : affine00077=(NestedInteger.clearedAll 3 raw00077 (IntegerComputedClassCell.leftNumerator ![(13/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/1600),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00077_transform
theorem leaf00077_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00077=true := by decide +kernel
#print axioms leaf00077_sign
theorem leaf00077_log : RationalLog.accepts (242532295/268435456) (-217917273/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00077_log
def leaf00077 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (15029054109/500000000000) (242532295/268435456) (-217917273/4294967296) 1 8 ![52,0,4] ![(13/1600),0,(1/2)] ![(1/3200),1,(1/2)] affine00077
theorem leaf00077_checked : FastNestedCellData.accepts 1 0 4 leaf00077=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (15029054109/500000000000) (242532295/268435456) (-217917273/4294967296) 1 8 ![52,0,4] ![(13/1600),0,(1/2)] ![(1/3200),1,(1/2)] 108295747976037474838668902400000000000 100786607746576448912966698788741709824 3353058915604721538399469568000000000000 raw00077 affine00077
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00077_raw leaf00077_rectangular
    leaf00077_transform leaf00077_sign leaf00077_log
#print axioms leaf00077_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
