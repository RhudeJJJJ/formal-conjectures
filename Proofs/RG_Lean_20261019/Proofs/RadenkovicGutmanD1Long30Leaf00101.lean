/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00101 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 14030014832499676628235971461120000000000 11764145562776957415281272187299999776768 154675661453843554865957044224000000000000))
theorem leaf00101_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 14030014832499676628235971461120000000000 11764145562776957415281272187299999776768 154675661453843554865957044224000000000000 raw00101=true := by decide +kernel
#print axioms leaf00101_raw
theorem leaf00101_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00101=true := by decide +kernel
#print axioms leaf00101_rectangular
def affine00101 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00101 (IntegerComputedClassCell.leftNumerator ![(19/8000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/8000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/8000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00101_transform : affine00101=(NestedInteger.clearedAll 3 raw00101 (IntegerComputedClassCell.leftNumerator ![(19/8000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/8000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/8000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00101_transform
theorem leaf00101_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00101=true := by decide +kernel
#print axioms leaf00101_sign
theorem leaf00101_log : RationalLog.accepts (1673388975/2147483648) (-267840475/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00101_log
def leaf00101 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (76056862807/1000000000000) (1673388975/2147483648) (-267840475/2147483648) 1 8 ![60,0,4] ![(19/8000),0,(1/16)] ![(3/32000),1,(1/16)] affine00101
theorem leaf00101_checked : FastNestedCellData.accepts 1 2 4 leaf00101=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (76056862807/1000000000000) (1673388975/2147483648) (-267840475/2147483648) 1 8 ![60,0,4] ![(19/8000),0,(1/16)] ![(3/32000),1,(1/16)] 14030014832499676628235971461120000000000 11764145562776957415281272187299999776768 154675661453843554865957044224000000000000 raw00101 affine00101
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00101_raw leaf00101_rectangular
    leaf00101_transform leaf00101_sign leaf00101_log
#print axioms leaf00101_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
