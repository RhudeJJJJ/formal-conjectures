/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00643 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 123563333785404880711162265600000000000 85890729642458027380823917706342301696 500883161581442272903928217600000000000))
theorem leaf00643_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 123563333785404880711162265600000000000 85890729642458027380823917706342301696 500883161581442272903928217600000000000 raw00643=true := by decide +kernel
#print axioms leaf00643_raw
theorem leaf00643_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00643=true := by decide +kernel
#print axioms leaf00643_rectangular
def affine00643 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00643 (IntegerComputedClassCell.leftNumerator ![(149/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(149/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(149/6400),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00643_transform : affine00643=(NestedInteger.clearedAll 3 raw00643 (IntegerComputedClassCell.leftNumerator ![(149/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(149/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(149/6400),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00643_transform
theorem leaf00643_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00643=true := by decide +kernel
#print axioms leaf00643_sign
theorem leaf00643_log : RationalLog.accepts (159280351/268435456) (-1120867603/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00643_log
def leaf00643 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (17147857271/100000000000) (159280351/268435456) (-1120867603/4294967296) 1 8 ![60,0,4] ![(149/6400),0,(1/4)] ![(3/6400),1,(1/4)] affine00643
theorem leaf00643_checked : FastNestedCellData.accepts 1 2 4 leaf00643=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (17147857271/100000000000) (159280351/268435456) (-1120867603/4294967296) 1 8 ![60,0,4] ![(149/6400),0,(1/4)] ![(3/6400),1,(1/4)] 123563333785404880711162265600000000000 85890729642458027380823917706342301696 500883161581442272903928217600000000000 raw00643 affine00643
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00643_raw leaf00643_rectangular
    leaf00643_transform leaf00643_sign leaf00643_log
#print axioms leaf00643_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
