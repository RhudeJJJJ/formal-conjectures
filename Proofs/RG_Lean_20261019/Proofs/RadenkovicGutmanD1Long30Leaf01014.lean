/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01014 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6296278153741910266726567641088000000000000 4537964773697292547395015150726361663930368 13295263130354804326271419416576000000000000))
theorem leaf01014_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6296278153741910266726567641088000000000000 4537964773697292547395015150726361663930368 13295263130354804326271419416576000000000000 raw01014=true := by decide +kernel
#print axioms leaf01014_raw
theorem leaf01014_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01014=true := by decide +kernel
#print axioms leaf01014_rectangular
def affine01014 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01014 (IntegerComputedClassCell.leftNumerator ![(13/80),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/80),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/80),0,(1/2)] ![(1/80),1,(1/2)]))
theorem leaf01014_transform : affine01014=(NestedInteger.clearedAll 3 raw01014 (IntegerComputedClassCell.leftNumerator ![(13/80),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/80),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/80),0,(1/2)] ![(1/80),1,(1/2)])) := by decide +kernel
#print axioms leaf01014_transform
theorem leaf01014_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01014=true := by decide +kernel
#print axioms leaf01014_sign
theorem leaf01014_log : RationalLog.accepts (2307831267/4294967296) (-1333878801/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01014_log
def leaf01014 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (341321922643/1000000000000) (2307831267/4294967296) (-1333878801/4294967296) 1 8 ![60,0,4] ![(13/80),0,(1/2)] ![(1/80),1,(1/2)] affine01014
theorem leaf01014_checked : FastNestedCellData.accepts 1 2 4 leaf01014=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (341321922643/1000000000000) (2307831267/4294967296) (-1333878801/4294967296) 1 8 ![60,0,4] ![(13/80),0,(1/2)] ![(1/80),1,(1/2)] 6296278153741910266726567641088000000000000 4537964773697292547395015150726361663930368 13295263130354804326271419416576000000000000 raw01014 affine01014
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01014_raw leaf01014_rectangular
    leaf01014_transform leaf01014_sign leaf01014_log
#print axioms leaf01014_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
