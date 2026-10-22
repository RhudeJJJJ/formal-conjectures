/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00716 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11516923309049119546804289929216000000000000 3116394741893591672763247265493517212844032 4991553272842935197912983928832000000000000))
theorem leaf00716_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11516923309049119546804289929216000000000000 3116394741893591672763247265493517212844032 4991553272842935197912983928832000000000000 raw00716=true := by decide +kernel
#print axioms leaf00716_raw
theorem leaf00716_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00716=true := by decide +kernel
#print axioms leaf00716_rectangular
def affine00716 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00716 (IntegerComputedClassCell.leftNumerator ![(97/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(97/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(97/3200),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00716_transform : affine00716=(NestedInteger.clearedAll 3 raw00716 (IntegerComputedClassCell.leftNumerator ![(97/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(97/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(97/3200),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00716_transform
theorem leaf00716_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00716=true := by decide +kernel
#print axioms leaf00716_sign
theorem leaf00716_log : RationalLog.accepts (715485117/4294967296) (-3848802811/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00716_log
def leaf00716 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (624333663601/1000000000000) (715485117/4294967296) (-3848802811/4294967296) 3 8 ![60,0,4] ![(97/3200),0,(1/16)] ![(3/6400),1,(1/16)] affine00716
theorem leaf00716_checked : FastNestedCellData.accepts 1 2 4 leaf00716=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (624333663601/1000000000000) (715485117/4294967296) (-3848802811/4294967296) 3 8 ![60,0,4] ![(97/3200),0,(1/16)] ![(3/6400),1,(1/16)] 11516923309049119546804289929216000000000000 3116394741893591672763247265493517212844032 4991553272842935197912983928832000000000000 raw00716 affine00716
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00716_raw leaf00716_rectangular
    leaf00716_transform leaf00716_sign leaf00716_log
#print axioms leaf00716_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
