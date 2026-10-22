/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01072 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 24069138788381874220687163392000000000000 24513594532523640881850923125372807544832 73388194682212378581670035456000000000000))
theorem leaf01072_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 24069138788381874220687163392000000000000 24513594532523640881850923125372807544832 73388194682212378581670035456000000000000 raw01072=true := by decide +kernel
#print axioms leaf01072_raw
theorem leaf01072_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01072=true := by decide +kernel
#print axioms leaf01072_rectangular
def affine01072 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01072 (IntegerComputedClassCell.leftNumerator ![(7/20),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/20),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/20),0,(1/8)] ![(3/160),1,(1/8)]))
theorem leaf01072_transform : affine01072=(NestedInteger.clearedAll 3 raw01072 (IntegerComputedClassCell.leftNumerator ![(7/20),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/20),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/20),0,(1/8)] ![(3/160),1,(1/8)])) := by decide +kernel
#print axioms leaf01072_transform
theorem leaf01072_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01072=true := by decide +kernel
#print axioms leaf01072_sign
theorem leaf01072_log : RationalLog.accepts (409875441/536870912) (-579615251/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01072_log
def leaf01072 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (167013200411/500000000000) (409875441/536870912) (-579615251/4294967296) 1 8 ![60,0,4] ![(7/20),0,(1/8)] ![(3/160),1,(1/8)] affine01072
theorem leaf01072_checked : FastNestedCellData.accepts 1 2 4 leaf01072=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (167013200411/500000000000) (409875441/536870912) (-579615251/4294967296) 1 8 ![60,0,4] ![(7/20),0,(1/8)] ![(3/160),1,(1/8)] 24069138788381874220687163392000000000000 24513594532523640881850923125372807544832 73388194682212378581670035456000000000000 raw01072 affine01072
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01072_raw leaf01072_rectangular
    leaf01072_transform leaf01072_sign leaf01072_log
#print axioms leaf01072_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
