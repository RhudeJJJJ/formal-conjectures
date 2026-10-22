/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01007 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 31778022903540290063485317939200000000000 19348541396149389656445452161404094119936 35098705677991103072361775104000000000000))
theorem leaf01007_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 31778022903540290063485317939200000000000 19348541396149389656445452161404094119936 35098705677991103072361775104000000000000 raw01007=true := by decide +kernel
#print axioms leaf01007_raw
theorem leaf01007_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01007=true := by decide +kernel
#print axioms leaf01007_rectangular
def affine01007 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01007 (IntegerComputedClassCell.leftNumerator ![(5/32),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(5/32),0,(1/8)] ![(1/160),1,(1/8)]))
theorem leaf01007_transform : affine01007=(NestedInteger.clearedAll 3 raw01007 (IntegerComputedClassCell.leftNumerator ![(5/32),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(5/32),0,(1/8)] ![(1/160),1,(1/8)])) := by decide +kernel
#print axioms leaf01007_transform
theorem leaf01007_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01007=true := by decide +kernel
#print axioms leaf01007_sign
theorem leaf01007_log : RationalLog.accepts (210720315/536870912) (-62761953/134217728) 2 8=true := by decide +kernel
#print axioms leaf01007_log
def leaf01007 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (551260823509/1000000000000) (210720315/536870912) (-62761953/134217728) 2 8 ![60,0,4] ![(5/32),0,(1/8)] ![(1/160),1,(1/8)] affine01007
theorem leaf01007_checked : FastNestedCellData.accepts 1 2 4 leaf01007=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (551260823509/1000000000000) (210720315/536870912) (-62761953/134217728) 2 8 ![60,0,4] ![(5/32),0,(1/8)] ![(1/160),1,(1/8)] 31778022903540290063485317939200000000000 19348541396149389656445452161404094119936 35098705677991103072361775104000000000000 raw01007 affine01007
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01007_raw leaf01007_rectangular
    leaf01007_transform leaf01007_sign leaf01007_log
#print axioms leaf01007_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
