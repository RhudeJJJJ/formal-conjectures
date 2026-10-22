/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00809 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 58734471449190339458510094336000000000000 43289742534324509174800649011633430986752 283250329067215625921698463744000000000000))
theorem leaf00809_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 58734471449190339458510094336000000000000 43289742534324509174800649011633430986752 283250329067215625921698463744000000000000 raw00809=true := by decide +kernel
#print axioms leaf00809_raw
theorem leaf00809_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00809=true := by decide +kernel
#print axioms leaf00809_rectangular
def affine00809 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00809 (IntegerComputedClassCell.leftNumerator ![(139/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(139/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(139/3200),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00809_transform : affine00809=(NestedInteger.clearedAll 3 raw00809 (IntegerComputedClassCell.leftNumerator ![(139/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(139/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(139/3200),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00809_transform
theorem leaf00809_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00809=true := by decide +kernel
#print axioms leaf00809_sign
theorem leaf00809_log : RationalLog.accepts (2745906459/4294967296) (-960639691/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00809_log
def leaf00809 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (38208024927/250000000000) (2745906459/4294967296) (-960639691/4294967296) 1 8 ![60,0,4] ![(139/3200),0,(1/2)] ![(3/3200),1,(1/2)] affine00809
theorem leaf00809_checked : FastNestedCellData.accepts 1 2 4 leaf00809=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (38208024927/250000000000) (2745906459/4294967296) (-960639691/4294967296) 1 8 ![60,0,4] ![(139/3200),0,(1/2)] ![(3/3200),1,(1/2)] 58734471449190339458510094336000000000000 43289742534324509174800649011633430986752 283250329067215625921698463744000000000000 raw00809 affine00809
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00809_raw leaf00809_rectangular
    leaf00809_transform leaf00809_sign leaf00809_log
#print axioms leaf00809_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
