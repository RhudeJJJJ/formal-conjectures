/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00220 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1485281262036513759661687151001600000000000 738472464261040741919170883288328830976 1834320933265790057842737152000000000000))
theorem leaf00220_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1485281262036513759661687151001600000000000 738472464261040741919170883288328830976 1834320933265790057842737152000000000000 raw00220=true := by decide +kernel
#print axioms leaf00220_raw
theorem leaf00220_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00220=true := by decide +kernel
#print axioms leaf00220_rectangular
def affine00220 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00220 (IntegerComputedClassCell.leftNumerator ![(37/8000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/8000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/8000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00220_transform : affine00220=(NestedInteger.clearedAll 3 raw00220 (IntegerComputedClassCell.leftNumerator ![(37/8000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/8000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/8000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00220_transform
theorem leaf00220_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00220=true := by decide +kernel
#print axioms leaf00220_sign
theorem leaf00220_log : RationalLog.accepts (1522495/4294967296) (-2132679159/536870912) 12 8=true := by decide +kernel
#print axioms leaf00220_log
def leaf00220 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (402586292763/1000000000000) (1522495/4294967296) (-2132679159/536870912) 12 8 ![60,0,4] ![(37/8000),0,0] ![(3/32000),1,(1/16)] affine00220
theorem leaf00220_checked : FastNestedCellData.accepts 1 2 4 leaf00220=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (402586292763/1000000000000) (1522495/4294967296) (-2132679159/536870912) 12 8 ![60,0,4] ![(37/8000),0,0] ![(3/32000),1,(1/16)] 1485281262036513759661687151001600000000000 738472464261040741919170883288328830976 1834320933265790057842737152000000000000 raw00220 affine00220
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00220_raw leaf00220_rectangular
    leaf00220_transform leaf00220_sign leaf00220_log
#print axioms leaf00220_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
