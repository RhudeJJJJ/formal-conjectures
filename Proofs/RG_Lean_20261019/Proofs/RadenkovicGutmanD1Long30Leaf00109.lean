/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00109 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 669169234650698863823814656000000000000 654374665875347630829345210903042195456 70464482795542533480420212736000000000000))
theorem leaf00109_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 669169234650698863823814656000000000000 654374665875347630829345210903042195456 70464482795542533480420212736000000000000 raw00109=true := by decide +kernel
#print axioms leaf00109_raw
theorem leaf00109_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00109=true := by decide +kernel
#print axioms leaf00109_rectangular
def affine00109 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00109 (IntegerComputedClassCell.leftNumerator ![(79/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(79/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(79/32000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00109_transform : affine00109=(NestedInteger.clearedAll 3 raw00109 (IntegerComputedClassCell.leftNumerator ![(79/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(79/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(79/32000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00109_transform
theorem leaf00109_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00109=true := by decide +kernel
#print axioms leaf00109_sign
theorem leaf00109_log : RationalLog.accepts (520170697/536870912) (-67861931/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00109_log
def leaf00109 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4643294323/500000000000) (520170697/536870912) (-67861931/4294967296) 1 8 ![60,0,4] ![(79/32000),0,(1/2)] ![(3/32000),1,(1/2)] affine00109
theorem leaf00109_checked : FastNestedCellData.accepts 1 2 4 leaf00109=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4643294323/500000000000) (520170697/536870912) (-67861931/4294967296) 1 8 ![60,0,4] ![(79/32000),0,(1/2)] ![(3/32000),1,(1/2)] 669169234650698863823814656000000000000 654374665875347630829345210903042195456 70464482795542533480420212736000000000000 raw00109 affine00109
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00109_raw leaf00109_rectangular
    leaf00109_transform leaf00109_sign leaf00109_log
#print axioms leaf00109_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
