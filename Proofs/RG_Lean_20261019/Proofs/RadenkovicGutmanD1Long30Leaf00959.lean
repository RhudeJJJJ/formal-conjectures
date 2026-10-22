/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00959 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 20580280108921703722618191872000000000000 13598879859614829085820451218932767916032 47613665076885167499185750016000000000000))
theorem leaf00959_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 20580280108921703722618191872000000000000 13598879859614829085820451218932767916032 47613665076885167499185750016000000000000 raw00959=true := by decide +kernel
#print axioms leaf00959_raw
theorem leaf00959_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00959=true := by decide +kernel
#print axioms leaf00959_rectangular
def affine00959 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00959 (IntegerComputedClassCell.leftNumerator ![(1/10),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/10),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/10),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00959_transform : affine00959=(NestedInteger.clearedAll 3 raw00959 (IntegerComputedClassCell.leftNumerator ![(1/10),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/10),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/10),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00959_transform
theorem leaf00959_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00959=true := by decide +kernel
#print axioms leaf00959_sign
theorem leaf00959_log : RationalLog.accepts (137969443/268435456) (-1429318475/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00959_log
def leaf00959 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (285608760377/1000000000000) (137969443/268435456) (-1429318475/4294967296) 1 8 ![60,0,4] ![(1/10),0,(1/2)] ![(1/320),1,(1/2)] affine00959
theorem leaf00959_checked : FastNestedCellData.accepts 1 2 4 leaf00959=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (285608760377/1000000000000) (137969443/268435456) (-1429318475/4294967296) 1 8 ![60,0,4] ![(1/10),0,(1/2)] ![(1/320),1,(1/2)] 20580280108921703722618191872000000000000 13598879859614829085820451218932767916032 47613665076885167499185750016000000000000 raw00959 affine00959
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00959_raw leaf00959_rectangular
    leaf00959_transform leaf00959_sign leaf00959_log
#print axioms leaf00959_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
