/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01071 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 395089658685845372829165420544000000000000 403709136376672233374079696060098768011264 1178074228728475023225552633856000000000000))
theorem leaf01071_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 395089658685845372829165420544000000000000 403709136376672233374079696060098768011264 1178074228728475023225552633856000000000000 raw01071=true := by decide +kernel
#print axioms leaf01071_raw
theorem leaf01071_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01071=true := by decide +kernel
#print axioms leaf01071_rectangular
def affine01071 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01071 (IntegerComputedClassCell.leftNumerator ![(7/20),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/20),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/20),0,(1/16)] ![(3/160),1,(1/16)]))
theorem leaf01071_transform : affine01071=(NestedInteger.clearedAll 3 raw01071 (IntegerComputedClassCell.leftNumerator ![(7/20),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/20),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/20),0,(1/16)] ![(3/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01071_transform
theorem leaf01071_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01071=true := by decide +kernel
#print axioms leaf01071_sign
theorem leaf01071_log : RationalLog.accepts (817143701/1073741824) (-586456111/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01071_log
def leaf01071 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (342685653019/1000000000000) (817143701/1073741824) (-586456111/4294967296) 1 8 ![60,0,4] ![(7/20),0,(1/16)] ![(3/160),1,(1/16)] affine01071
theorem leaf01071_checked : FastNestedCellData.accepts 1 2 4 leaf01071=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (342685653019/1000000000000) (817143701/1073741824) (-586456111/4294967296) 1 8 ![60,0,4] ![(7/20),0,(1/16)] ![(3/160),1,(1/16)] 395089658685845372829165420544000000000000 403709136376672233374079696060098768011264 1178074228728475023225552633856000000000000 raw01071 affine01071
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01071_raw leaf01071_rectangular
    leaf01071_transform leaf01071_sign leaf01071_log
#print axioms leaf01071_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
