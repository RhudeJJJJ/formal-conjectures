/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00082 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 77373396033867079498290167808000000000000 66238806941358055929216687967617096351744 987007794368569758697513811968000000000000))
theorem leaf00082_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 77373396033867079498290167808000000000000 66238806941358055929216687967617096351744 987007794368569758697513811968000000000000 raw00082=true := by decide +kernel
#print axioms leaf00082_raw
theorem leaf00082_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00082=true := by decide +kernel
#print axioms leaf00082_rectangular
def affine00082 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00082 (IntegerComputedClassCell.leftNumerator ![(7/800),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/800),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/800),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00082_transform : affine00082=(NestedInteger.clearedAll 3 raw00082 (IntegerComputedClassCell.leftNumerator ![(7/800),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/800),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/800),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00082_transform
theorem leaf00082_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00082=true := by decide +kernel
#print axioms leaf00082_sign
theorem leaf00082_log : RationalLog.accepts (1722825233/2147483648) (-236578885/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00082_log
def leaf00082 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (33555361629/500000000000) (1722825233/2147483648) (-236578885/2147483648) 1 8 ![52,0,4] ![(7/800),0,(1/4)] ![(1/3200),1,(1/4)] affine00082
theorem leaf00082_checked : FastNestedCellData.accepts 1 0 4 leaf00082=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (33555361629/500000000000) (1722825233/2147483648) (-236578885/2147483648) 1 8 ![52,0,4] ![(7/800),0,(1/4)] ![(1/3200),1,(1/4)] 77373396033867079498290167808000000000000 66238806941358055929216687967617096351744 987007794368569758697513811968000000000000 raw00082 affine00082
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00082_raw leaf00082_rectangular
    leaf00082_transform leaf00082_sign leaf00082_log
#print axioms leaf00082_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
