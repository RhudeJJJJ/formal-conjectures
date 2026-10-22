/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01025 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2573111011790837100981333786624000000000000 1809092058106996922903496820166565845532672 3242364791954124884737641152512000000000000))
theorem leaf01025_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2573111011790837100981333786624000000000000 1809092058106996922903496820166565845532672 3242364791954124884737641152512000000000000 raw01025=true := by decide +kernel
#print axioms leaf01025_raw
theorem leaf01025_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01025=true := by decide +kernel
#print axioms leaf01025_rectangular
def affine01025 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01025 (IntegerComputedClassCell.leftNumerator ![(1/5),0,0] ![(3/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/5),0,0] ![(3/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/5),0,0] ![(3/320),1,(1/16)]))
theorem leaf01025_transform : affine01025=(NestedInteger.clearedAll 3 raw01025 (IntegerComputedClassCell.leftNumerator ![(1/5),0,0] ![(3/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/5),0,0] ![(3/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/5),0,0] ![(3/320),1,(1/16)])) := by decide +kernel
#print axioms leaf01025_transform
theorem leaf01025_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01025=true := by decide +kernel
#print axioms leaf01025_sign
theorem leaf01025_log : RationalLog.accepts (1938238573/4294967296) (-854338107/2147483648) 2 8=true := by decide +kernel
#print axioms leaf01025_log
def leaf01025 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (278977254903/500000000000) (1938238573/4294967296) (-854338107/2147483648) 2 8 ![60,0,4] ![(1/5),0,0] ![(3/320),1,(1/16)] affine01025
theorem leaf01025_checked : FastNestedCellData.accepts 1 2 4 leaf01025=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (278977254903/500000000000) (1938238573/4294967296) (-854338107/2147483648) 2 8 ![60,0,4] ![(1/5),0,0] ![(3/320),1,(1/16)] 2573111011790837100981333786624000000000000 1809092058106996922903496820166565845532672 3242364791954124884737641152512000000000000 raw01025 affine01025
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01025_raw leaf01025_rectangular
    leaf01025_transform leaf01025_sign leaf01025_log
#print axioms leaf01025_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
