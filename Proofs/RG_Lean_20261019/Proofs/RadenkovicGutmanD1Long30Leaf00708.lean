/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00708 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3887186267223926785723045249024000000000000 2523383640052036558718071623799609655033856 11974783045595706994600710242304000000000000))
theorem leaf00708_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3887186267223926785723045249024000000000000 2523383640052036558718071623799609655033856 11974783045595706994600710242304000000000000 raw00708=true := by decide +kernel
#print axioms leaf00708_raw
theorem leaf00708_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00708=true := by decide +kernel
#print axioms leaf00708_rectangular
def affine00708 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00708 (IntegerComputedClassCell.leftNumerator ![(47/1600),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(47/1600),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(47/1600),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00708_transform : affine00708=(NestedInteger.clearedAll 3 raw00708 (IntegerComputedClassCell.leftNumerator ![(47/1600),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(47/1600),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(47/1600),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00708_transform
theorem leaf00708_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00708=true := by decide +kernel
#print axioms leaf00708_sign
theorem leaf00708_log : RationalLog.accepts (2302832541/4294967296) (-1338535261/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00708_log
def leaf00708 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (210724789789/1000000000000) (2302832541/4294967296) (-1338535261/4294967296) 1 8 ![60,0,4] ![(47/1600),0,(1/4)] ![(3/6400),1,(1/4)] affine00708
theorem leaf00708_checked : FastNestedCellData.accepts 1 2 4 leaf00708=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (210724789789/1000000000000) (2302832541/4294967296) (-1338535261/4294967296) 1 8 ![60,0,4] ![(47/1600),0,(1/4)] ![(3/6400),1,(1/4)] 3887186267223926785723045249024000000000000 2523383640052036558718071623799609655033856 11974783045595706994600710242304000000000000 raw00708 affine00708
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00708_raw leaf00708_rectangular
    leaf00708_transform leaf00708_sign leaf00708_log
#print axioms leaf00708_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
