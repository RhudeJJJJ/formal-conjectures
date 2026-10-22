/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00701 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11293207324968444879265907867648000000000000 3117587586513967722453257628990394268123136 5092383295633659935099833024512000000000000))
theorem leaf00701_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11293207324968444879265907867648000000000000 3117587586513967722453257628990394268123136 5092383295633659935099833024512000000000000 raw00701=true := by decide +kernel
#print axioms leaf00701_raw
theorem leaf00701_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00701=true := by decide +kernel
#print axioms leaf00701_rectangular
def affine00701 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00701 (IntegerComputedClassCell.leftNumerator ![(37/1280),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/1280),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/1280),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00701_transform : affine00701=(NestedInteger.clearedAll 3 raw00701 (IntegerComputedClassCell.leftNumerator ![(37/1280),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/1280),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/1280),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00701_transform
theorem leaf00701_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00701=true := by decide +kernel
#print axioms leaf00701_sign
theorem leaf00701_log : RationalLog.accepts (735428899/4294967296) (-3789761899/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00701_log
def leaf00701 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (612205995803/1000000000000) (735428899/4294967296) (-3789761899/4294967296) 3 8 ![60,0,4] ![(37/1280),0,(1/16)] ![(3/6400),1,(1/16)] affine00701
theorem leaf00701_checked : FastNestedCellData.accepts 1 2 4 leaf00701=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (612205995803/1000000000000) (735428899/4294967296) (-3789761899/4294967296) 3 8 ![60,0,4] ![(37/1280),0,(1/16)] ![(3/6400),1,(1/16)] 11293207324968444879265907867648000000000000 3117587586513967722453257628990394268123136 5092383295633659935099833024512000000000000 raw00701 affine00701
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00701_raw leaf00701_rectangular
    leaf00701_transform leaf00701_sign leaf00701_log
#print axioms leaf00701_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
