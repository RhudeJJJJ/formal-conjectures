/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01116 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 8103635904785522636496463462400000000000 9750635940949142096684299657230843641856 55489748019276127139264043417600000000000))
theorem leaf01116_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 8103635904785522636496463462400000000000 9750635940949142096684299657230843641856 55489748019276127139264043417600000000000 raw01116=true := by decide +kernel
#print axioms leaf01116_raw
theorem leaf01116_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01116=true := by decide +kernel
#print axioms leaf01116_rectangular
def affine01116 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01116 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/8),0,(1/2)] ![(1/16),1,(1/4)]))
theorem leaf01116_transform : affine01116=(NestedInteger.clearedAll 3 raw01116 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/8),0,(1/2)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf01116_transform
theorem leaf01116_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01116=true := by decide +kernel
#print axioms leaf01116_sign
theorem leaf01116_log : RationalLog.accepts (4395508529/4294967296) (24845623/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01116_log
def leaf01116 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (8785979653/50000000000) (4395508529/4294967296) (24845623/2147483648) 0 8 ![60,0,4] ![(5/8),0,(1/2)] ![(1/16),1,(1/4)] affine01116
theorem leaf01116_checked : FastNestedCellData.accepts 1 2 4 leaf01116=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (8785979653/50000000000) (4395508529/4294967296) (24845623/2147483648) 0 8 ![60,0,4] ![(5/8),0,(1/2)] ![(1/16),1,(1/4)] 8103635904785522636496463462400000000000 9750635940949142096684299657230843641856 55489748019276127139264043417600000000000 raw01116 affine01116
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01116_raw leaf01116_rectangular
    leaf01116_transform leaf01116_sign leaf01116_log
#print axioms leaf01116_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
