/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00750 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 253325866991019704696807882752000000000000 10590055053621876994423238984659839746048 12049205980536424719089401856000000000000))
theorem leaf00750_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 253325866991019704696807882752000000000000 10590055053621876994423238984659839746048 12049205980536424719089401856000000000000 raw00750=true := by decide +kernel
#print axioms leaf00750_raw
theorem leaf00750_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00750=true := by decide +kernel
#print axioms leaf00750_rectangular
def affine00750 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00750 (IntegerComputedClassCell.leftNumerator ![(43/1280),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(43/1280),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(43/1280),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00750_transform : affine00750=(NestedInteger.clearedAll 3 raw00750 (IntegerComputedClassCell.leftNumerator ![(43/1280),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(43/1280),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(43/1280),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00750_transform
theorem leaf00750_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00750=true := by decide +kernel
#print axioms leaf00750_sign
theorem leaf00750_log : RationalLog.accepts (11944961/536870912) (-4086068957/2147483648) 6 8=true := by decide +kernel
#print axioms leaf00750_log
def leaf00750 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (878900657083/1000000000000) (11944961/536870912) (-4086068957/2147483648) 6 8 ![60,0,4] ![(43/1280),0,0] ![(3/6400),1,(1/16)] affine00750
theorem leaf00750_checked : FastNestedCellData.accepts 1 2 4 leaf00750=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (878900657083/1000000000000) (11944961/536870912) (-4086068957/2147483648) 6 8 ![60,0,4] ![(43/1280),0,0] ![(3/6400),1,(1/16)] 253325866991019704696807882752000000000000 10590055053621876994423238984659839746048 12049205980536424719089401856000000000000 raw00750 affine00750
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00750_raw leaf00750_rectangular
    leaf00750_transform leaf00750_sign leaf00750_log
#print axioms leaf00750_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
