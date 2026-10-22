/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00308 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 309900649317774896188302032896000000000000 202445049023932760909143762784064301432832 753155087072907927018581000192000000000000))
theorem leaf00308_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 309900649317774896188302032896000000000000 202445049023932760909143762784064301432832 753155087072907927018581000192000000000000 raw00308=true := by decide +kernel
#print axioms leaf00308_raw
theorem leaf00308_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00308=true := by decide +kernel
#print axioms leaf00308_rectangular
def affine00308 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00308 (IntegerComputedClassCell.leftNumerator ![(7/80),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/80),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/80),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00308_transform : affine00308=(NestedInteger.clearedAll 3 raw00308 (IntegerComputedClassCell.leftNumerator ![(7/80),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/80),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/80),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00308_transform
theorem leaf00308_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00308=true := by decide +kernel
#print axioms leaf00308_sign
theorem leaf00308_log : RationalLog.accepts (2211325867/4294967296) (-178201329/536870912) 1 8=true := by decide +kernel
#print axioms leaf00308_log
def leaf00308 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (67198991449/250000000000) (2211325867/4294967296) (-178201329/536870912) 1 8 ![52,0,4] ![(7/80),0,(1/2)] ![(1/320),1,(1/2)] affine00308
theorem leaf00308_checked : FastNestedCellData.accepts 1 0 4 leaf00308=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (67198991449/250000000000) (2211325867/4294967296) (-178201329/536870912) 1 8 ![52,0,4] ![(7/80),0,(1/2)] ![(1/320),1,(1/2)] 309900649317774896188302032896000000000000 202445049023932760909143762784064301432832 753155087072907927018581000192000000000000 raw00308 affine00308
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00308_raw leaf00308_rectangular
    leaf00308_transform leaf00308_sign leaf00308_log
#print axioms leaf00308_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
