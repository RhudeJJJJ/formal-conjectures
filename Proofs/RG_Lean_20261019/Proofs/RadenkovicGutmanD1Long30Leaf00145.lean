/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00145 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 341075667463850322478646689792000000000000 65338344694359701849082111514575372288 220860031539851794279563264000000000000))
theorem leaf00145_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 341075667463850322478646689792000000000000 65338344694359701849082111514575372288 220860031539851794279563264000000000000 raw00145=true := by decide +kernel
#print axioms leaf00145_raw
theorem leaf00145_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00145=true := by decide +kernel
#print axioms leaf00145_rectangular
def affine00145 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00145 (IntegerComputedClassCell.leftNumerator ![(103/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(103/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(103/32000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00145_transform : affine00145=(NestedInteger.clearedAll 3 raw00145 (IntegerComputedClassCell.leftNumerator ![(103/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(103/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(103/32000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00145_transform
theorem leaf00145_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00145=true := by decide +kernel
#print axioms leaf00145_sign
theorem leaf00145_log : RationalLog.accepts (158733/1073741824) (-18939596325/4294967296) 13 8=true := by decide +kernel
#print axioms leaf00145_log
def leaf00145 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (295835983717/1000000000000) (158733/1073741824) (-18939596325/4294967296) 13 8 ![60,0,4] ![(103/32000),0,0] ![(3/32000),1,(1/16)] affine00145
theorem leaf00145_checked : FastNestedCellData.accepts 1 2 4 leaf00145=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (295835983717/1000000000000) (158733/1073741824) (-18939596325/4294967296) 13 8 ![60,0,4] ![(103/32000),0,0] ![(3/32000),1,(1/16)] 341075667463850322478646689792000000000000 65338344694359701849082111514575372288 220860031539851794279563264000000000000 raw00145 affine00145
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00145_raw leaf00145_rectangular
    leaf00145_transform leaf00145_sign leaf00145_log
#print axioms leaf00145_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
