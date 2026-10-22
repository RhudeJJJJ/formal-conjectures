/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00011 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 26879700734403053850969348505600000000000 24654792313457013285931891845203717259264 676794207630010220199691262361600000000000))
theorem leaf00011_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 26879700734403053850969348505600000000000 24654792313457013285931891845203717259264 676794207630010220199691262361600000000000 raw00011=true := by decide +kernel
#print axioms leaf00011_raw
theorem leaf00011_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00011=true := by decide +kernel
#print axioms leaf00011_rectangular
def affine00011 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00011 (IntegerComputedClassCell.leftNumerator ![(9/8000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/8000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/8000),0,(1/16)] ![(1/16000),1,(1/16)]))
theorem leaf00011_transform : affine00011=(NestedInteger.clearedAll 3 raw00011 (IntegerComputedClassCell.leftNumerator ![(9/8000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/8000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/8000),0,(1/16)] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00011_transform
theorem leaf00011_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00011=true := by decide +kernel
#print axioms leaf00011_sign
theorem leaf00011_log : RationalLog.accepts (3800995131/4294967296) (-65595451/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00011_log
def leaf00011 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (7285757483/200000000000) (3800995131/4294967296) (-65595451/1073741824) 1 8 ![60,0,4] ![(9/8000),0,(1/16)] ![(1/16000),1,(1/16)] affine00011
theorem leaf00011_checked : FastNestedCellData.accepts 1 2 4 leaf00011=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (7285757483/200000000000) (3800995131/4294967296) (-65595451/1073741824) 1 8 ![60,0,4] ![(9/8000),0,(1/16)] ![(1/16000),1,(1/16)] 26879700734403053850969348505600000000000 24654792313457013285931891845203717259264 676794207630010220199691262361600000000000 raw00011 affine00011
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00011_raw leaf00011_rectangular
    leaf00011_transform leaf00011_sign leaf00011_log
#print axioms leaf00011_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
