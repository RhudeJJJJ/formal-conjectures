/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00227 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2637727324327267339523921543168000000000000 1968191744110878404949893548852515912548352 13764398259346679348225453850624000000000000))
theorem leaf00227_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2637727324327267339523921543168000000000000 1968191744110878404949893548852515912548352 13764398259346679348225453850624000000000000 raw00227=true := by decide +kernel
#print axioms leaf00227_raw
theorem leaf00227_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00227=true := by decide +kernel
#print axioms leaf00227_rectangular
def affine00227 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00227 (IntegerComputedClassCell.leftNumerator ![(13/320),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/320),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/320),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00227_transform : affine00227=(NestedInteger.clearedAll 3 raw00227 (IntegerComputedClassCell.leftNumerator ![(13/320),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/320),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/320),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00227_transform
theorem leaf00227_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00227=true := by decide +kernel
#print axioms leaf00227_sign
theorem leaf00227_log : RationalLog.accepts (2803847403/4294967296) (-114474679/536870912) 1 8=true := by decide +kernel
#print axioms leaf00227_log
def leaf00227 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (142991484773/1000000000000) (2803847403/4294967296) (-114474679/536870912) 1 8 ![52,0,4] ![(13/320),0,(1/2)] ![(3/3200),1,(1/2)] affine00227
theorem leaf00227_checked : FastNestedCellData.accepts 1 0 4 leaf00227=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (142991484773/1000000000000) (2803847403/4294967296) (-114474679/536870912) 1 8 ![52,0,4] ![(13/320),0,(1/2)] ![(3/3200),1,(1/2)] 2637727324327267339523921543168000000000000 1968191744110878404949893548852515912548352 13764398259346679348225453850624000000000000 raw00227 affine00227
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00227_raw leaf00227_rectangular
    leaf00227_transform leaf00227_sign leaf00227_log
#print axioms leaf00227_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
