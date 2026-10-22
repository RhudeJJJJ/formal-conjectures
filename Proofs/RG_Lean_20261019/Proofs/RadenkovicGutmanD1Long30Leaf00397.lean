/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00397 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2786622787790432761300108967936000000000000 1995786431705946189969229900497485542981632 13211605708806223748452992417792000000000000))
theorem leaf00397_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2786622787790432761300108967936000000000000 1995786431705946189969229900497485542981632 13211605708806223748452992417792000000000000 raw00397=true := by decide +kernel
#print axioms leaf00397_raw
theorem leaf00397_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00397=true := by decide +kernel
#print axioms leaf00397_rectangular
def affine00397 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00397 (IntegerComputedClassCell.leftNumerator ![(63/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(63/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(63/6400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00397_transform : affine00397=(NestedInteger.clearedAll 3 raw00397 (IntegerComputedClassCell.leftNumerator ![(63/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(63/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(63/6400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00397_transform
theorem leaf00397_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00397=true := by decide +kernel
#print axioms leaf00397_sign
theorem leaf00397_log : RationalLog.accepts (2672370087/4294967296) (-1018934189/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00397_log
def leaf00397 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (151063124021/1000000000000) (2672370087/4294967296) (-1018934189/4294967296) 1 8 ![60,0,4] ![(63/6400),0,(1/8)] ![(1/6400),1,(1/8)] affine00397
theorem leaf00397_checked : FastNestedCellData.accepts 1 2 4 leaf00397=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (151063124021/1000000000000) (2672370087/4294967296) (-1018934189/4294967296) 1 8 ![60,0,4] ![(63/6400),0,(1/8)] ![(1/6400),1,(1/8)] 2786622787790432761300108967936000000000000 1995786431705946189969229900497485542981632 13211605708806223748452992417792000000000000 raw00397 affine00397
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00397_raw leaf00397_rectangular
    leaf00397_transform leaf00397_sign leaf00397_log
#print axioms leaf00397_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
