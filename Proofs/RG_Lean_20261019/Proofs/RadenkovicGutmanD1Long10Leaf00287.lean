/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00287 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1016572469453095283589430378496000000000000 686476704884188555304866202202838187114496 3114204955396529563500653051904000000000000))
theorem leaf00287_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1016572469453095283589430378496000000000000 686476704884188555304866202202838187114496 3114204955396529563500653051904000000000000 raw00287=true := by decide +kernel
#print axioms leaf00287_raw
theorem leaf00287_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00287=true := by decide +kernel
#print axioms leaf00287_rectangular
def affine00287 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00287 (IntegerComputedClassCell.leftNumerator ![(43/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(43/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(43/640),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00287_transform : affine00287=(NestedInteger.clearedAll 3 raw00287 (IntegerComputedClassCell.leftNumerator ![(43/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(43/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(43/640),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00287_transform
theorem leaf00287_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00287=true := by decide +kernel
#print axioms leaf00287_sign
theorem leaf00287_log : RationalLog.accepts (2376473729/4294967296) (-317734269/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00287_log
def leaf00287 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (110217007987/500000000000) (2376473729/4294967296) (-317734269/1073741824) 1 8 ![52,0,4] ![(43/640),0,(1/2)] ![(1/640),1,(1/2)] affine00287
theorem leaf00287_checked : FastNestedCellData.accepts 1 0 4 leaf00287=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (110217007987/500000000000) (2376473729/4294967296) (-317734269/1073741824) 1 8 ![52,0,4] ![(43/640),0,(1/2)] ![(1/640),1,(1/2)] 1016572469453095283589430378496000000000000 686476704884188555304866202202838187114496 3114204955396529563500653051904000000000000 raw00287 affine00287
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00287_raw leaf00287_rectangular
    leaf00287_transform leaf00287_sign leaf00287_log
#print axioms leaf00287_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
