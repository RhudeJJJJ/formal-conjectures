/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00358 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 8821460260362900222241274855424000000000000 6429545930090714350647158814758535998472192 13444960900120301931315360432128000000000000))
theorem leaf00358_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 8821460260362900222241274855424000000000000 6429545930090714350647158814758535998472192 13444960900120301931315360432128000000000000 raw00358=true := by decide +kernel
#print axioms leaf00358_raw
theorem leaf00358_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00358=true := by decide +kernel
#print axioms leaf00358_rectangular
def affine00358 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00358 (IntegerComputedClassCell.leftNumerator ![(1/5),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/5),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/5),0,(1/4)] ![(3/160),1,(1/4)]))
theorem leaf00358_transform : affine00358=(NestedInteger.clearedAll 3 raw00358 (IntegerComputedClassCell.leftNumerator ![(1/5),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/5),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/5),0,(1/4)] ![(3/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00358_transform
theorem leaf00358_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00358=true := by decide +kernel
#print axioms leaf00358_sign
theorem leaf00358_log : RationalLog.accepts (2117692337/4294967296) (-1518522193/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00358_log
def leaf00358 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (478212318939/1000000000000) (2117692337/4294967296) (-1518522193/4294967296) 2 8 ![52,0,4] ![(1/5),0,(1/4)] ![(3/160),1,(1/4)] affine00358
theorem leaf00358_checked : FastNestedCellData.accepts 1 0 4 leaf00358=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (478212318939/1000000000000) (2117692337/4294967296) (-1518522193/4294967296) 2 8 ![52,0,4] ![(1/5),0,(1/4)] ![(3/160),1,(1/4)] 8821460260362900222241274855424000000000000 6429545930090714350647158814758535998472192 13444960900120301931315360432128000000000000 raw00358 affine00358
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00358_raw leaf00358_rectangular
    leaf00358_transform leaf00358_sign leaf00358_log
#print axioms leaf00358_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
