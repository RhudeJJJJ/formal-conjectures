/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00258 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1030839121796670810966949101568000000000000 72239896670871175437892945574778573422592 107727033380031133080398856192000000000000))
theorem leaf00258_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1030839121796670810966949101568000000000000 72239896670871175437892945574778573422592 107727033380031133080398856192000000000000 raw00258=true := by decide +kernel
#print axioms leaf00258_raw
theorem leaf00258_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00258=true := by decide +kernel
#print axioms leaf00258_rectangular
def affine00258 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00258 (IntegerComputedClassCell.leftNumerator ![(17/320),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/320),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/320),0,0] ![(1/640),1,(1/4)]))
theorem leaf00258_transform : affine00258=(NestedInteger.clearedAll 3 raw00258 (IntegerComputedClassCell.leftNumerator ![(17/320),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/320),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/320),0,0] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00258_transform
theorem leaf00258_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00258=true := by decide +kernel
#print axioms leaf00258_sign
theorem leaf00258_log : RationalLog.accepts (90084087/2147483648) (-6810333335/4294967296) 5 8=true := by decide +kernel
#print axioms leaf00258_log
def leaf00258 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (670582809201/1000000000000) (90084087/2147483648) (-6810333335/4294967296) 5 8 ![52,0,4] ![(17/320),0,0] ![(1/640),1,(1/4)] affine00258
theorem leaf00258_checked : FastNestedCellData.accepts 1 0 4 leaf00258=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (670582809201/1000000000000) (90084087/2147483648) (-6810333335/4294967296) 5 8 ![52,0,4] ![(17/320),0,0] ![(1/640),1,(1/4)] 1030839121796670810966949101568000000000000 72239896670871175437892945574778573422592 107727033380031133080398856192000000000000 raw00258 affine00258
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00258_raw leaf00258_rectangular
    leaf00258_transform leaf00258_sign leaf00258_log
#print axioms leaf00258_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
