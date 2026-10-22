/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00337 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 189754548649689778759724433408000000000000 143961877654634615690209576481707266146304 1166255711375306816400165699584000000000000))
theorem leaf00337_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 189754548649689778759724433408000000000000 143961877654634615690209576481707266146304 1166255711375306816400165699584000000000000 raw00337=true := by decide +kernel
#print axioms leaf00337_raw
theorem leaf00337_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00337=true := by decide +kernel
#print axioms leaf00337_rectangular
def affine00337 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00337 (IntegerComputedClassCell.leftNumerator ![(51/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(51/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(51/6400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00337_transform : affine00337=(NestedInteger.clearedAll 3 raw00337 (IntegerComputedClassCell.leftNumerator ![(51/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(51/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(51/6400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00337_transform
theorem leaf00337_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00337=true := by decide +kernel
#print axioms leaf00337_sign
theorem leaf00337_log : RationalLog.accepts (1450225479/2147483648) (-52690891/268435456) 1 8=true := by decide +kernel
#print axioms leaf00337_log
def leaf00337 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (123439376331/1000000000000) (1450225479/2147483648) (-52690891/268435456) 1 8 ![60,0,4] ![(51/6400),0,(1/8)] ![(1/6400),1,(1/8)] affine00337
theorem leaf00337_checked : FastNestedCellData.accepts 1 2 4 leaf00337=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (123439376331/1000000000000) (1450225479/2147483648) (-52690891/268435456) 1 8 ![60,0,4] ![(51/6400),0,(1/8)] ![(1/6400),1,(1/8)] 189754548649689778759724433408000000000000 143961877654634615690209576481707266146304 1166255711375306816400165699584000000000000 raw00337 affine00337
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00337_raw leaf00337_rectangular
    leaf00337_transform leaf00337_sign leaf00337_log
#print axioms leaf00337_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
