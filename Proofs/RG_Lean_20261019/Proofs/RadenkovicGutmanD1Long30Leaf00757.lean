/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00757 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 120935626838091318408773632000000000000 51728661205032991843828253338583957504 120397306307871087874015232000000000000))
theorem leaf00757_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 120935626838091318408773632000000000000 51728661205032991843828253338583957504 120397306307871087874015232000000000000 raw00757=true := by decide +kernel
#print axioms leaf00757_raw
theorem leaf00757_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00757=true := by decide +kernel
#print axioms leaf00757_rectangular
def affine00757 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00757 (IntegerComputedClassCell.leftNumerator ![(109/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(109/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(109/3200),0,(1/8)] ![(3/3200),1,(1/8)]))
theorem leaf00757_transform : affine00757=(NestedInteger.clearedAll 3 raw00757 (IntegerComputedClassCell.leftNumerator ![(109/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(109/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(109/3200),0,(1/8)] ![(3/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00757_transform
theorem leaf00757_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00757=true := by decide +kernel
#print axioms leaf00757_sign
theorem leaf00757_log : RationalLog.accepts (10039157/33554432) (-80978645/134217728) 2 8=true := by decide +kernel
#print axioms leaf00757_log
def leaf00757 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (214824827861/500000000000) (10039157/33554432) (-80978645/134217728) 2 8 ![60,0,4] ![(109/3200),0,(1/8)] ![(3/3200),1,(1/8)] affine00757
theorem leaf00757_checked : FastNestedCellData.accepts 1 2 4 leaf00757=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (214824827861/500000000000) (10039157/33554432) (-80978645/134217728) 2 8 ![60,0,4] ![(109/3200),0,(1/8)] ![(3/3200),1,(1/8)] 120935626838091318408773632000000000000 51728661205032991843828253338583957504 120397306307871087874015232000000000000 raw00757 affine00757
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00757_raw leaf00757_rectangular
    leaf00757_transform leaf00757_sign leaf00757_log
#print axioms leaf00757_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
