/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00537 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 10727426515007744202780128051200000000000 6500508755228660867719410492374184361984 27945477228124547058817092812800000000000))
theorem leaf00537_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 10727426515007744202780128051200000000000 6500508755228660867719410492374184361984 27945477228124547058817092812800000000000 raw00537=true := by decide +kernel
#print axioms leaf00537_raw
theorem leaf00537_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00537=true := by decide +kernel
#print axioms leaf00537_rectangular
def affine00537 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00537 (IntegerComputedClassCell.leftNumerator ![(1/64),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/64),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/64),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00537_transform : affine00537=(NestedInteger.clearedAll 3 raw00537 (IntegerComputedClassCell.leftNumerator ![(1/64),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/64),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/64),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00537_transform
theorem leaf00537_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00537=true := by decide +kernel
#print axioms leaf00537_sign
theorem leaf00537_log : RationalLog.accepts (527867081/1073741824) (-1524843057/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00537_log
def leaf00537 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (46522796531/200000000000) (527867081/1073741824) (-1524843057/4294967296) 2 8 ![60,0,4] ![(1/64),0,(1/8)] ![(1/3200),1,(1/8)] affine00537
theorem leaf00537_checked : FastNestedCellData.accepts 1 2 4 leaf00537=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (46522796531/200000000000) (527867081/1073741824) (-1524843057/4294967296) 2 8 ![60,0,4] ![(1/64),0,(1/8)] ![(1/3200),1,(1/8)] 10727426515007744202780128051200000000000 6500508755228660867719410492374184361984 27945477228124547058817092812800000000000 raw00537 affine00537
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00537_raw leaf00537_rectangular
    leaf00537_transform leaf00537_sign leaf00537_log
#print axioms leaf00537_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
