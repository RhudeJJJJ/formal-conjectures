/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00103 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 512387728929243913813007269888000000000000 423795323191558549040081335559122795364352 5085760531961823709833029746688000000000000))
theorem leaf00103_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 512387728929243913813007269888000000000000 423795323191558549040081335559122795364352 5085760531961823709833029746688000000000000 raw00103=true := by decide +kernel
#print axioms leaf00103_raw
theorem leaf00103_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00103=true := by decide +kernel
#print axioms leaf00103_rectangular
def affine00103 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00103 (IntegerComputedClassCell.leftNumerator ![(7/640),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/640),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/640),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00103_transform : affine00103=(NestedInteger.clearedAll 3 raw00103 (IntegerComputedClassCell.leftNumerator ![(7/640),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/640),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/640),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00103_transform
theorem leaf00103_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00103=true := by decide +kernel
#print axioms leaf00103_sign
theorem leaf00103_log : RationalLog.accepts (3279114771/4294967296) (-579542397/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00103_log
def leaf00103 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (83329783329/1000000000000) (3279114771/4294967296) (-579542397/4294967296) 1 8 ![52,0,4] ![(7/640),0,(1/4)] ![(1/3200),1,(1/4)] affine00103
theorem leaf00103_checked : FastNestedCellData.accepts 1 0 4 leaf00103=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (83329783329/1000000000000) (3279114771/4294967296) (-579542397/4294967296) 1 8 ![52,0,4] ![(7/640),0,(1/4)] ![(1/3200),1,(1/4)] 512387728929243913813007269888000000000000 423795323191558549040081335559122795364352 5085760531961823709833029746688000000000000 raw00103 affine00103
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00103_raw leaf00103_rectangular
    leaf00103_transform leaf00103_sign leaf00103_log
#print axioms leaf00103_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
