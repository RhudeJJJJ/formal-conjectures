/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00119 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 184069833214310586907254325248000000000000 179714178002389402890389725672296274722816 18010237691514478491532024348672000000000000))
theorem leaf00119_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 184069833214310586907254325248000000000000 179714178002389402890389725672296274722816 18010237691514478491532024348672000000000000 raw00119=true := by decide +kernel
#print axioms leaf00119_raw
theorem leaf00119_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00119=true := by decide +kernel
#print axioms leaf00119_rectangular
def affine00119 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00119 (IntegerComputedClassCell.leftNumerator ![(17/6400),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/6400),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/6400),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00119_transform : affine00119=(NestedInteger.clearedAll 3 raw00119 (IntegerComputedClassCell.leftNumerator ![(17/6400),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/6400),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/6400),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00119_transform
theorem leaf00119_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00119=true := by decide +kernel
#print axioms leaf00119_sign
theorem leaf00119_log : RationalLog.accepts (4151905669/4294967296) (-36374649/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00119_log
def leaf00119 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (9978445653/1000000000000) (4151905669/4294967296) (-36374649/2147483648) 1 8 ![60,0,4] ![(17/6400),0,(1/2)] ![(3/32000),1,(1/2)] affine00119
theorem leaf00119_checked : FastNestedCellData.accepts 1 2 4 leaf00119=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (9978445653/1000000000000) (4151905669/4294967296) (-36374649/2147483648) 1 8 ![60,0,4] ![(17/6400),0,(1/2)] ![(3/32000),1,(1/2)] 184069833214310586907254325248000000000000 179714178002389402890389725672296274722816 18010237691514478491532024348672000000000000 raw00119 affine00119
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00119_raw leaf00119_rectangular
    leaf00119_transform leaf00119_sign leaf00119_log
#print axioms leaf00119_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
