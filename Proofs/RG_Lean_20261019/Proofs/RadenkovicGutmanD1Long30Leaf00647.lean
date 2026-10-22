/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00647 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1222936954679204134624879758540800000000000 615563989956589318207591546916916854521856 1857029725084946385514344218624000000000000))
theorem leaf00647_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1222936954679204134624879758540800000000000 615563989956589318207591546916916854521856 1857029725084946385514344218624000000000000 raw00647=true := by decide +kernel
#print axioms leaf00647_raw
theorem leaf00647_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00647=true := by decide +kernel
#print axioms leaf00647_rectangular
def affine00647 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00647 (IntegerComputedClassCell.leftNumerator ![(19/800),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/800),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/800),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00647_transform : affine00647=(NestedInteger.clearedAll 3 raw00647 (IntegerComputedClassCell.leftNumerator ![(19/800),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/800),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/800),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00647_transform
theorem leaf00647_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00647=true := by decide +kernel
#print axioms leaf00647_sign
theorem leaf00647_log : RationalLog.accepts (1623660005/4294967296) (-2088988579/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00647_log
def leaf00647 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (331477725769/1000000000000) (1623660005/4294967296) (-2088988579/4294967296) 2 8 ![60,0,4] ![(19/800),0,(1/8)] ![(3/6400),1,(1/8)] affine00647
theorem leaf00647_checked : FastNestedCellData.accepts 1 2 4 leaf00647=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (331477725769/1000000000000) (1623660005/4294967296) (-2088988579/4294967296) 2 8 ![60,0,4] ![(19/800),0,(1/8)] ![(3/6400),1,(1/8)] 1222936954679204134624879758540800000000000 615563989956589318207591546916916854521856 1857029725084946385514344218624000000000000 raw00647 affine00647
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00647_raw leaf00647_rectangular
    leaf00647_transform leaf00647_sign leaf00647_log
#print axioms leaf00647_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
