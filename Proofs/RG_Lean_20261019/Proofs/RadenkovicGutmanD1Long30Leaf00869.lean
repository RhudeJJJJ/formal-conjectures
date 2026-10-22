/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00869 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7208248433854238233288182333440000000000 5013963892559578838668681722265478365184 25662630684722984706622305075200000000000))
theorem leaf00869_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7208248433854238233288182333440000000000 5013963892559578838668681722265478365184 25662630684722984706622305075200000000000 raw00869=true := by decide +kernel
#print axioms leaf00869_raw
theorem leaf00869_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00869=true := by decide +kernel
#print axioms leaf00869_rectangular
def affine00869 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00869 (IntegerComputedClassCell.leftNumerator ![(37/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/640),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00869_transform : affine00869=(NestedInteger.clearedAll 3 raw00869 (IntegerComputedClassCell.leftNumerator ![(37/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/640),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00869_transform
theorem leaf00869_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00869=true := by decide +kernel
#print axioms leaf00869_sign
theorem leaf00869_log : RationalLog.accepts (1249612465/2147483648) (-1162783587/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00869_log
def leaf00869 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (39075993059/200000000000) (1249612465/2147483648) (-1162783587/4294967296) 1 8 ![60,0,4] ![(37/640),0,(1/2)] ![(1/640),1,(1/2)] affine00869
theorem leaf00869_checked : FastNestedCellData.accepts 1 2 4 leaf00869=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (39075993059/200000000000) (1249612465/2147483648) (-1162783587/4294967296) 1 8 ![60,0,4] ![(37/640),0,(1/2)] ![(1/640),1,(1/2)] 7208248433854238233288182333440000000000 5013963892559578838668681722265478365184 25662630684722984706622305075200000000000 raw00869 affine00869
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00869_raw leaf00869_rectangular
    leaf00869_transform leaf00869_sign leaf00869_log
#print axioms leaf00869_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
