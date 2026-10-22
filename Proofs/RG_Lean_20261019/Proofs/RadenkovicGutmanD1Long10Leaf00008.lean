/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00008 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 871965850642712707284525383680000000000 857997947028402574204106721113287950336 145209985303301583481209461145600000000000))
theorem leaf00008_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 871965850642712707284525383680000000000 857997947028402574204106721113287950336 145209985303301583481209461145600000000000 raw00008=true := by decide +kernel
#print axioms leaf00008_raw
theorem leaf00008_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00008=true := by decide +kernel
#print axioms leaf00008_rectangular
def affine00008 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00008 (IntegerComputedClassCell.leftNumerator ![(3/2000),0,(1/2)] ![(1/4000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/2000),0,(1/2)] ![(1/4000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/2000),0,(1/2)] ![(1/4000),1,(1/2)]))
theorem leaf00008_transform : affine00008=(NestedInteger.clearedAll 3 raw00008 (IntegerComputedClassCell.leftNumerator ![(3/2000),0,(1/2)] ![(1/4000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/2000),0,(1/2)] ![(1/4000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/2000),0,(1/2)] ![(1/4000),1,(1/2)])) := by decide +kernel
#print axioms leaf00008_transform
theorem leaf00008_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00008=true := by decide +kernel
#print axioms leaf00008_sign
theorem leaf00008_log : RationalLog.accepts (4201342445/4294967296) (-47330227/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00008_log
def leaf00008 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (1181734087/200000000000) (4201342445/4294967296) (-47330227/4294967296) 1 8 ![52,0,4] ![(3/2000),0,(1/2)] ![(1/4000),1,(1/2)] affine00008
theorem leaf00008_checked : FastNestedCellData.accepts 1 0 4 leaf00008=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (1181734087/200000000000) (4201342445/4294967296) (-47330227/4294967296) 1 8 ![52,0,4] ![(3/2000),0,(1/2)] ![(1/4000),1,(1/2)] 871965850642712707284525383680000000000 857997947028402574204106721113287950336 145209985303301583481209461145600000000000 raw00008 affine00008
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00008_raw leaf00008_rectangular
    leaf00008_transform leaf00008_sign leaf00008_log
#print axioms leaf00008_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
