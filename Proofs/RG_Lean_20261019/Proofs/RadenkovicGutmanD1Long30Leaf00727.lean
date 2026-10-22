/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00727 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 29151432097570867492195139584000000000000 13003329894628040522238195639005831233536 32142114444059749780285292544000000000000))
theorem leaf00727_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 29151432097570867492195139584000000000000 13003329894628040522238195639005831233536 32142114444059749780285292544000000000000 raw00727=true := by decide +kernel
#print axioms leaf00727_raw
theorem leaf00727_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00727=true := by decide +kernel
#print axioms leaf00727_rectangular
def affine00727 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00727 (IntegerComputedClassCell.leftNumerator ![(1/32),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/32),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/32),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00727_transform : affine00727=(NestedInteger.clearedAll 3 raw00727 (IntegerComputedClassCell.leftNumerator ![(1/32),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/32),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/32),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00727_transform
theorem leaf00727_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00727=true := by decide +kernel
#print axioms leaf00727_sign
theorem leaf00727_log : RationalLog.accepts (1364002161/4294967296) (-2463208477/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00727_log
def leaf00727 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (25284836809/62500000000) (1364002161/4294967296) (-2463208477/4294967296) 2 8 ![60,0,4] ![(1/32),0,(1/8)] ![(3/6400),1,(1/8)] affine00727
theorem leaf00727_checked : FastNestedCellData.accepts 1 2 4 leaf00727=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (25284836809/62500000000) (1364002161/4294967296) (-2463208477/4294967296) 2 8 ![60,0,4] ![(1/32),0,(1/8)] ![(3/6400),1,(1/8)] 29151432097570867492195139584000000000000 13003329894628040522238195639005831233536 32142114444059749780285292544000000000000 raw00727 affine00727
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00727_raw leaf00727_rectangular
    leaf00727_transform leaf00727_sign leaf00727_log
#print axioms leaf00727_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
