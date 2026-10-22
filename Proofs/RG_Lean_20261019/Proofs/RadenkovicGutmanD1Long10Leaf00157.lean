/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00157 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 17917605540847342134933585920000000000 12805978639529951081364775000571117568 82401011270124188579439575040000000000))
theorem leaf00157_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 17917605540847342134933585920000000000 12805978639529951081364775000571117568 82401011270124188579439575040000000000 raw00157=true := by decide +kernel
#print axioms leaf00157_raw
theorem leaf00157_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00157=true := by decide +kernel
#print axioms leaf00157_rectangular
def affine00157 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00157 (IntegerComputedClassCell.leftNumerator ![(67/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(67/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(67/3200),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00157_transform : affine00157=(NestedInteger.clearedAll 3 raw00157 (IntegerComputedClassCell.leftNumerator ![(67/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(67/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(67/3200),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00157_transform
theorem leaf00157_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00157=true := by decide +kernel
#print axioms leaf00157_sign
theorem leaf00157_log : RationalLog.accepts (166049047/268435456) (-1031495035/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00157_log
def leaf00157 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (6216418193/40000000000) (166049047/268435456) (-1031495035/4294967296) 1 8 ![52,0,4] ![(67/3200),0,(1/4)] ![(3/6400),1,(1/4)] affine00157
theorem leaf00157_checked : FastNestedCellData.accepts 1 0 4 leaf00157=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (6216418193/40000000000) (166049047/268435456) (-1031495035/4294967296) 1 8 ![52,0,4] ![(67/3200),0,(1/4)] ![(3/6400),1,(1/4)] 17917605540847342134933585920000000000 12805978639529951081364775000571117568 82401011270124188579439575040000000000 raw00157 affine00157
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00157_raw leaf00157_rectangular
    leaf00157_transform leaf00157_sign leaf00157_log
#print axioms leaf00157_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
