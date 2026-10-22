/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00370 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1552742149904249409077204798668800000000000 1393111740371258479691452578525277493133312 3310063521144629783786860576768000000000000))
theorem leaf00370_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1552742149904249409077204798668800000000000 1393111740371258479691452578525277493133312 3310063521144629783786860576768000000000000 raw00370=true := by decide +kernel
#print axioms leaf00370_raw
theorem leaf00370_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00370=true := by decide +kernel
#print axioms leaf00370_rectangular
def affine00370 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00370 (IntegerComputedClassCell.leftNumerator ![(11/40),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/40),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/40),0,(1/4)] ![(3/80),1,(1/4)]))
theorem leaf00370_transform : affine00370=(NestedInteger.clearedAll 3 raw00370 (IntegerComputedClassCell.leftNumerator ![(11/40),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/40),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/40),0,(1/4)] ![(3/80),1,(1/4)])) := by decide +kernel
#print axioms leaf00370_transform
theorem leaf00370_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00370=true := by decide +kernel
#print axioms leaf00370_sign
theorem leaf00370_log : RationalLog.accepts (2712012185/4294967296) (-987312253/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00370_log
def leaf00370 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (420871603059/1000000000000) (2712012185/4294967296) (-987312253/4294967296) 1 8 ![52,0,4] ![(11/40),0,(1/4)] ![(3/80),1,(1/4)] affine00370
theorem leaf00370_checked : FastNestedCellData.accepts 1 0 4 leaf00370=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (420871603059/1000000000000) (2712012185/4294967296) (-987312253/4294967296) 1 8 ![52,0,4] ![(11/40),0,(1/4)] ![(3/80),1,(1/4)] 1552742149904249409077204798668800000000000 1393111740371258479691452578525277493133312 3310063521144629783786860576768000000000000 raw00370 affine00370
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00370_raw leaf00370_rectangular
    leaf00370_transform leaf00370_sign leaf00370_log
#print axioms leaf00370_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
