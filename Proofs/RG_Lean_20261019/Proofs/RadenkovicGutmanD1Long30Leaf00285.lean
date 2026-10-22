/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00285 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 371823356089534851024997580800000000000 420461761450415150997136256813498368 814834851519400011995545600000000000))
theorem leaf00285_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 371823356089534851024997580800000000000 420461761450415150997136256813498368 814834851519400011995545600000000000 raw00285=true := by decide +kernel
#print axioms leaf00285_raw
theorem leaf00285_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00285=true := by decide +kernel
#print axioms leaf00285_rectangular
def affine00285 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00285 (IntegerComputedClassCell.leftNumerator ![(41/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/6400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00285_transform : affine00285=(NestedInteger.clearedAll 3 raw00285 (IntegerComputedClassCell.leftNumerator ![(41/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/6400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00285_transform
theorem leaf00285_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00285=true := by decide +kernel
#print axioms leaf00285_sign
theorem leaf00285_log : RationalLog.accepts (400459/536870912) (-3865954689/1073741824) 11 8=true := by decide +kernel
#print axioms leaf00285_log
def leaf00285 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (25800428189/50000000000) (400459/536870912) (-3865954689/1073741824) 11 8 ![60,0,4] ![(41/6400),0,0] ![(1/6400),1,(1/16)] affine00285
theorem leaf00285_checked : FastNestedCellData.accepts 1 2 4 leaf00285=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (25800428189/50000000000) (400459/536870912) (-3865954689/1073741824) 11 8 ![60,0,4] ![(41/6400),0,0] ![(1/6400),1,(1/16)] 371823356089534851024997580800000000000 420461761450415150997136256813498368 814834851519400011995545600000000000 raw00285 affine00285
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00285_raw leaf00285_rectangular
    leaf00285_transform leaf00285_sign leaf00285_log
#print axioms leaf00285_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
