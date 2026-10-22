/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00520 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3585589484162350863570012471296000000000000 27294122959441617995845426173467550547968 35104946004910681097483845632000000000000))
theorem leaf00520_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3585589484162350863570012471296000000000000 27294122959441617995845426173467550547968 35104946004910681097483845632000000000000 raw00520=true := by decide +kernel
#print axioms leaf00520_raw
theorem leaf00520_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00520=true := by decide +kernel
#print axioms leaf00520_rectangular
def affine00520 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00520 (IntegerComputedClassCell.leftNumerator ![(47/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(47/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(47/3200),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00520_transform : affine00520=(NestedInteger.clearedAll 3 raw00520 (IntegerComputedClassCell.leftNumerator ![(47/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(47/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(47/3200),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00520_transform
theorem leaf00520_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00520=true := by decide +kernel
#print axioms leaf00520_sign
theorem leaf00520_log : RationalLog.accepts (18393257/4294967296) (-11710690517/4294967296) 8 8=true := by decide +kernel
#print axioms leaf00520_log
def leaf00520 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (388750390837/500000000000) (18393257/4294967296) (-11710690517/4294967296) 8 8 ![60,0,4] ![(47/3200),0,0] ![(1/3200),1,(1/16)] affine00520
theorem leaf00520_checked : FastNestedCellData.accepts 1 2 4 leaf00520=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (388750390837/500000000000) (18393257/4294967296) (-11710690517/4294967296) 8 8 ![60,0,4] ![(47/3200),0,0] ![(1/3200),1,(1/16)] 3585589484162350863570012471296000000000000 27294122959441617995845426173467550547968 35104946004910681097483845632000000000000 raw00520 affine00520
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00520_raw leaf00520_rectangular
    leaf00520_transform leaf00520_sign leaf00520_log
#print axioms leaf00520_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
