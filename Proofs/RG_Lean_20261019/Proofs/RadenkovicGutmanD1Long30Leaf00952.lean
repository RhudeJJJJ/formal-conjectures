/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00952 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11056512614486824788437439086592000000000000 4865413302933286269586857734177068513492992 8117481265696353935322372898816000000000000))
theorem leaf00952_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11056512614486824788437439086592000000000000 4865413302933286269586857734177068513492992 8117481265696353935322372898816000000000000 raw00952=true := by decide +kernel
#print axioms leaf00952_raw
theorem leaf00952_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00952=true := by decide +kernel
#print axioms leaf00952_rectangular
def affine00952 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00952 (IntegerComputedClassCell.leftNumerator ![(31/320),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(31/320),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(31/320),0,(1/8)] ![(1/320),1,(1/8)]))
theorem leaf00952_transform : affine00952=(NestedInteger.clearedAll 3 raw00952 (IntegerComputedClassCell.leftNumerator ![(31/320),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(31/320),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(31/320),0,(1/8)] ![(1/320),1,(1/8)])) := by decide +kernel
#print axioms leaf00952_transform
theorem leaf00952_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00952=true := by decide +kernel
#print axioms leaf00952_sign
theorem leaf00952_log : RationalLog.accepts (1181710783/4294967296) (-1385643175/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00952_log
def leaf00952 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (599374749837/1000000000000) (1181710783/4294967296) (-1385643175/2147483648) 2 8 ![60,0,4] ![(31/320),0,(1/8)] ![(1/320),1,(1/8)] affine00952
theorem leaf00952_checked : FastNestedCellData.accepts 1 2 4 leaf00952=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (599374749837/1000000000000) (1181710783/4294967296) (-1385643175/2147483648) 2 8 ![60,0,4] ![(31/320),0,(1/8)] ![(1/320),1,(1/8)] 11056512614486824788437439086592000000000000 4865413302933286269586857734177068513492992 8117481265696353935322372898816000000000000 raw00952 affine00952
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00952_raw leaf00952_rectangular
    leaf00952_transform leaf00952_sign leaf00952_log
#print axioms leaf00952_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
