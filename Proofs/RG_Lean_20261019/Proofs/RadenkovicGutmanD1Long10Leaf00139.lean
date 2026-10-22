/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00139 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 608537901268428883642365771776000000000000 454049405388713494223968105945589480423424 3440925027252748611034489552896000000000000))
theorem leaf00139_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 608537901268428883642365771776000000000000 454049405388713494223968105945589480423424 3440925027252748611034489552896000000000000 raw00139=true := by decide +kernel
#print axioms leaf00139_raw
theorem leaf00139_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00139=true := by decide +kernel
#print axioms leaf00139_rectangular
def affine00139 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00139 (IntegerComputedClassCell.leftNumerator ![(7/400),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/400),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/400),0,(1/4)] ![(1/1600),1,(1/4)]))
theorem leaf00139_transform : affine00139=(NestedInteger.clearedAll 3 raw00139 (IntegerComputedClassCell.leftNumerator ![(7/400),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/400),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/400),0,(1/4)] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00139_transform
theorem leaf00139_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00139=true := by decide +kernel
#print axioms leaf00139_sign
theorem leaf00139_log : RationalLog.accepts (1415519783/2147483648) (-223767783/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00139_log
def leaf00139 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (131955622919/1000000000000) (1415519783/2147483648) (-223767783/1073741824) 1 8 ![52,0,4] ![(7/400),0,(1/4)] ![(1/1600),1,(1/4)] affine00139
theorem leaf00139_checked : FastNestedCellData.accepts 1 0 4 leaf00139=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (131955622919/1000000000000) (1415519783/2147483648) (-223767783/1073741824) 1 8 ![52,0,4] ![(7/400),0,(1/4)] ![(1/1600),1,(1/4)] 608537901268428883642365771776000000000000 454049405388713494223968105945589480423424 3440925027252748611034489552896000000000000 raw00139 affine00139
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00139_raw leaf00139_rectangular
    leaf00139_transform leaf00139_sign leaf00139_log
#print axioms leaf00139_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
