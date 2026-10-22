/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00426 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 365006748068281498858875256832000000000000 182889937760524708223960343481401168887808 577681764340619169519888236544000000000000))
theorem leaf00426_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 365006748068281498858875256832000000000000 182889937760524708223960343481401168887808 577681764340619169519888236544000000000000 raw00426=true := by decide +kernel
#print axioms leaf00426_raw
theorem leaf00426_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00426=true := by decide +kernel
#print axioms leaf00426_rectangular
def affine00426 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00426 (IntegerComputedClassCell.leftNumerator ![(69/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(69/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(69/6400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00426_transform : affine00426=(NestedInteger.clearedAll 3 raw00426 (IntegerComputedClassCell.leftNumerator ![(69/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(69/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(69/6400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00426_transform
theorem leaf00426_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00426=true := by decide +kernel
#print axioms leaf00426_sign
theorem leaf00426_log : RationalLog.accepts (817273241/2147483648) (-2074637973/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00426_log
def leaf00426 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (158296443691/500000000000) (817273241/2147483648) (-2074637973/4294967296) 2 8 ![60,0,4] ![(69/6400),0,(1/16)] ![(1/6400),1,(1/16)] affine00426
theorem leaf00426_checked : FastNestedCellData.accepts 1 2 4 leaf00426=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (158296443691/500000000000) (817273241/2147483648) (-2074637973/4294967296) 2 8 ![60,0,4] ![(69/6400),0,(1/16)] ![(1/6400),1,(1/16)] 365006748068281498858875256832000000000000 182889937760524708223960343481401168887808 577681764340619169519888236544000000000000 raw00426 affine00426
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00426_raw leaf00426_rectangular
    leaf00426_transform leaf00426_sign leaf00426_log
#print axioms leaf00426_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
