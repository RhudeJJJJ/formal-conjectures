/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00386 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 656449870042125941609838149632000000000 351543929725391887379192540052118831104 1234831705788572304244998144000000000000))
theorem leaf00386_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 656449870042125941609838149632000000000 351543929725391887379192540052118831104 1234831705788572304244998144000000000000 raw00386=true := by decide +kernel
#print axioms leaf00386_raw
theorem leaf00386_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00386=true := by decide +kernel
#print axioms leaf00386_rectangular
def affine00386 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00386 (IntegerComputedClassCell.leftNumerator ![(61/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(61/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(61/6400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00386_transform : affine00386=(NestedInteger.clearedAll 3 raw00386 (IntegerComputedClassCell.leftNumerator ![(61/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(61/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(61/6400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00386_transform
theorem leaf00386_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00386=true := by decide +kernel
#print axioms leaf00386_sign
theorem leaf00386_log : RationalLog.accepts (223794625/536870912) (-1879110325/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00386_log
def leaf00386 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (284689750091/1000000000000) (223794625/536870912) (-1879110325/4294967296) 2 8 ![60,0,4] ![(61/6400),0,(1/16)] ![(1/6400),1,(1/16)] affine00386
theorem leaf00386_checked : FastNestedCellData.accepts 1 2 4 leaf00386=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (284689750091/1000000000000) (223794625/536870912) (-1879110325/4294967296) 2 8 ![60,0,4] ![(61/6400),0,(1/16)] ![(1/6400),1,(1/16)] 656449870042125941609838149632000000000 351543929725391887379192540052118831104 1234831705788572304244998144000000000000 raw00386 affine00386
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00386_raw leaf00386_rectangular
    leaf00386_transform leaf00386_sign leaf00386_log
#print axioms leaf00386_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
