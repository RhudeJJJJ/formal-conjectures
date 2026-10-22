/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00706 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 454800701244114684319488215613440000000000 124678469734276392609342462852401750605824 202278652288661182717932601344000000000000))
theorem leaf00706_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 454800701244114684319488215613440000000000 124678469734276392609342462852401750605824 202278652288661182717932601344000000000000 raw00706=true := by decide +kernel
#print axioms leaf00706_raw
theorem leaf00706_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00706=true := by decide +kernel
#print axioms leaf00706_rectangular
def affine00706 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00706 (IntegerComputedClassCell.leftNumerator ![(47/1600),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(47/1600),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(47/1600),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00706_transform : affine00706=(NestedInteger.clearedAll 3 raw00706 (IntegerComputedClassCell.leftNumerator ![(47/1600),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(47/1600),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(47/1600),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00706_transform
theorem leaf00706_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00706=true := by decide +kernel
#print axioms leaf00706_sign
theorem leaf00706_log : RationalLog.accepts (728432725/4294967296) (-3810288817/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00706_log
def leaf00706 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (616369885421/1000000000000) (728432725/4294967296) (-3810288817/4294967296) 3 8 ![60,0,4] ![(47/1600),0,(1/16)] ![(3/6400),1,(1/16)] affine00706
theorem leaf00706_checked : FastNestedCellData.accepts 1 2 4 leaf00706=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (616369885421/1000000000000) (728432725/4294967296) (-3810288817/4294967296) 3 8 ![60,0,4] ![(47/1600),0,(1/16)] ![(3/6400),1,(1/16)] 454800701244114684319488215613440000000000 124678469734276392609342462852401750605824 202278652288661182717932601344000000000000 raw00706 affine00706
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00706_raw leaf00706_rectangular
    leaf00706_transform leaf00706_sign leaf00706_log
#print axioms leaf00706_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
