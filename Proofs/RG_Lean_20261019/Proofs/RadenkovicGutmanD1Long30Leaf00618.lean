/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00618 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 717760718373218670026264936448000000000000 513689780621875786870302444574229108097024 3300509373753614907366914916352000000000000))
theorem leaf00618_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 717760718373218670026264936448000000000000 513689780621875786870302444574229108097024 3300509373753614907366914916352000000000000 raw00618=true := by decide +kernel
#print axioms leaf00618_raw
theorem leaf00618_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00618=true := by decide +kernel
#print axioms leaf00618_rectangular
def affine00618 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00618 (IntegerComputedClassCell.leftNumerator ![(67/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(67/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(67/3200),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00618_transform : affine00618=(NestedInteger.clearedAll 3 raw00618 (IntegerComputedClassCell.leftNumerator ![(67/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(67/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(67/3200),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00618_transform
theorem leaf00618_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00618=true := by decide +kernel
#print axioms leaf00618_sign
theorem leaf00618_log : RationalLog.accepts (1329929777/2147483648) (-32156597/134217728) 1 8=true := by decide +kernel
#print axioms leaf00618_log
def leaf00618 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (155639546037/1000000000000) (1329929777/2147483648) (-32156597/134217728) 1 8 ![60,0,4] ![(67/3200),0,(1/4)] ![(3/6400),1,(1/4)] affine00618
theorem leaf00618_checked : FastNestedCellData.accepts 1 2 4 leaf00618=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (155639546037/1000000000000) (1329929777/2147483648) (-32156597/134217728) 1 8 ![60,0,4] ![(67/3200),0,(1/4)] ![(3/6400),1,(1/4)] 717760718373218670026264936448000000000000 513689780621875786870302444574229108097024 3300509373753614907366914916352000000000000 raw00618 affine00618
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00618_raw leaf00618_rectangular
    leaf00618_transform leaf00618_sign leaf00618_log
#print axioms leaf00618_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
