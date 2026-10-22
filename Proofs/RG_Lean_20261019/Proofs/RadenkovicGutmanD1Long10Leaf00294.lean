/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00294 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 203489018107183038771056607232000000000000 28293894134483711464857063939046086017024 40076657821816274998953771008000000000000))
theorem leaf00294_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 203489018107183038771056607232000000000000 28293894134483711464857063939046086017024 40076657821816274998953771008000000000000 raw00294=true := by decide +kernel
#print axioms leaf00294_raw
theorem leaf00294_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00294=true := by decide +kernel
#print axioms leaf00294_rectangular
def affine00294 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00294 (IntegerComputedClassCell.leftNumerator ![(3/40),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/40),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/40),0,0] ![(1/320),1,(1/4)]))
theorem leaf00294_transform : affine00294=(NestedInteger.clearedAll 3 raw00294 (IntegerComputedClassCell.leftNumerator ![(3/40),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/40),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/40),0,0] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00294_transform
theorem leaf00294_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00294=true := by decide +kernel
#print axioms leaf00294_sign
theorem leaf00294_log : RationalLog.accepts (175026587/2147483648) (-5383986785/4294967296) 4 8=true := by decide +kernel
#print axioms leaf00294_log
def leaf00294 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (176498588407/250000000000) (175026587/2147483648) (-5383986785/4294967296) 4 8 ![52,0,4] ![(3/40),0,0] ![(1/320),1,(1/4)] affine00294
theorem leaf00294_checked : FastNestedCellData.accepts 1 0 4 leaf00294=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (176498588407/250000000000) (175026587/2147483648) (-5383986785/4294967296) 4 8 ![52,0,4] ![(3/40),0,0] ![(1/320),1,(1/4)] 203489018107183038771056607232000000000000 28293894134483711464857063939046086017024 40076657821816274998953771008000000000000 raw00294 affine00294
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00294_raw leaf00294_rectangular
    leaf00294_transform leaf00294_sign leaf00294_log
#print axioms leaf00294_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
