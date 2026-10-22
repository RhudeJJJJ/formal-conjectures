/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00412 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 1272325766787229973122455175168000000000000 1701071400059527447955755495723134019960832 24662888693389498295661451280384000000000000))
theorem leaf00412_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 1272325766787229973122455175168000000000000 1701071400059527447955755495723134019960832 24662888693389498295661451280384000000000000 raw00412=true := by decide +kernel
#print axioms leaf00412_raw
theorem leaf00412_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00412=true := by decide +kernel
#print axioms leaf00412_rectangular
def affine00412 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00412 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(1/2)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(1/2)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/8),0,(1/2)] ![(1/8),1,(1/4)]))
theorem leaf00412_transform : affine00412=(NestedInteger.clearedAll 3 raw00412 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(1/2)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(1/2)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/8),0,(1/2)] ![(1/8),1,(1/4)])) := by decide +kernel
#print axioms leaf00412_transform
theorem leaf00412_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00412=true := by decide +kernel
#print axioms leaf00412_sign
theorem leaf00412_log : RationalLog.accepts (5371769623/4294967296) (120105245/1073741824) 0 8=true := by decide +kernel
#print axioms leaf00412_log
def leaf00412 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (68972918023/1000000000000) (5371769623/4294967296) (120105245/1073741824) 0 8 ![52,0,4] ![(5/8),0,(1/2)] ![(1/8),1,(1/4)] affine00412
theorem leaf00412_checked : FastNestedCellData.accepts 1 0 4 leaf00412=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (68972918023/1000000000000) (5371769623/4294967296) (120105245/1073741824) 0 8 ![52,0,4] ![(5/8),0,(1/2)] ![(1/8),1,(1/4)] 1272325766787229973122455175168000000000000 1701071400059527447955755495723134019960832 24662888693389498295661451280384000000000000 raw00412 affine00412
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00412_raw leaf00412_rectangular
    leaf00412_transform leaf00412_sign leaf00412_log
#print axioms leaf00412_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
