/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00486 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 694201880978118819604070400000000000 699502461829855942979480684108709888 4840519336349045451420336128000000000000))
theorem leaf00486_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 694201880978118819604070400000000000 699502461829855942979480684108709888 4840519336349045451420336128000000000000 raw00486=true := by decide +kernel
#print axioms leaf00486_raw
theorem leaf00486_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00486=true := by decide +kernel
#print axioms leaf00486_rectangular
def affine00486 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00486 (IntegerComputedClassCell.leftNumerator ![(1/16),0,0] ![(1/128),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/16),0,0] ![(1/128),1,1]) (IntegerComputedClassCell.denominator ![(1/16),0,0] ![(1/128),1,1]))
theorem leaf00486_transform : affine00486=(NestedInteger.clearedAll 3 raw00486 (IntegerComputedClassCell.leftNumerator ![(1/16),0,0] ![(1/128),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/16),0,0] ![(1/128),1,1]) (IntegerComputedClassCell.denominator ![(1/16),0,0] ![(1/128),1,1])) := by decide +kernel
#print axioms leaf00486_transform
theorem leaf00486_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00486=true := by decide +kernel
#print axioms leaf00486_sign
theorem leaf00486_log : RationalLog.accepts (1081784055/1073741824) (16024525/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00486_log
def leaf00486 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (36127449/250000000000) (1081784055/1073741824) (16024525/4294967296) 0 8 ![52,0,4] ![(1/16),0,0] ![(1/128),1,1] affine00486
theorem leaf00486_checked : FastNestedCellData.accepts 1 0 4 leaf00486=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (36127449/250000000000) (1081784055/1073741824) (16024525/4294967296) 0 8 ![52,0,4] ![(1/16),0,0] ![(1/128),1,1] 694201880978118819604070400000000000 699502461829855942979480684108709888 4840519336349045451420336128000000000000 raw00486 affine00486
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00486_raw leaf00486_rectangular
    leaf00486_transform leaf00486_sign leaf00486_log
#print axioms leaf00486_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
