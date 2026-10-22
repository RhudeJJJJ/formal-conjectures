/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00578 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 31265611223863520464208291430400000000000 23291985469605199787988759595528835039232 171778704344675155692031574016000000000000))
theorem leaf00578_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 31265611223863520464208291430400000000000 23291985469605199787988759595528835039232 171778704344675155692031574016000000000000 raw00578=true := by decide +kernel
#print axioms leaf00578_raw
theorem leaf00578_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00578=true := by decide +kernel
#print axioms leaf00578_rectangular
def affine00578 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00578 (IntegerComputedClassCell.leftNumerator ![(29/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/1600),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00578_transform : affine00578=(NestedInteger.clearedAll 3 raw00578 (IntegerComputedClassCell.leftNumerator ![(29/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/1600),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00578_transform
theorem leaf00578_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00578=true := by decide +kernel
#print axioms leaf00578_sign
theorem leaf00578_log : RationalLog.accepts (2817583215/4294967296) (-113162847/536870912) 1 8=true := by decide +kernel
#print axioms leaf00578_log
def leaf00578 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (33898243613/250000000000) (2817583215/4294967296) (-113162847/536870912) 1 8 ![60,0,4] ![(29/1600),0,(1/4)] ![(1/3200),1,(1/4)] affine00578
theorem leaf00578_checked : FastNestedCellData.accepts 1 2 4 leaf00578=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (33898243613/250000000000) (2817583215/4294967296) (-113162847/536870912) 1 8 ![60,0,4] ![(29/1600),0,(1/4)] ![(1/3200),1,(1/4)] 31265611223863520464208291430400000000000 23291985469605199787988759595528835039232 171778704344675155692031574016000000000000 raw00578 affine00578
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00578_raw leaf00578_rectangular
    leaf00578_transform leaf00578_sign leaf00578_log
#print axioms leaf00578_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
