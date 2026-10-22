/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00700 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 251405591723156472780189335552000000000000 7795801214522283112596019484131388817408 8937695860560142859948261376000000000000))
theorem leaf00700_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 251405591723156472780189335552000000000000 7795801214522283112596019484131388817408 8937695860560142859948261376000000000000 raw00700=true := by decide +kernel
#print axioms leaf00700_raw
theorem leaf00700_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00700=true := by decide +kernel
#print axioms leaf00700_rectangular
def affine00700 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00700 (IntegerComputedClassCell.leftNumerator ![(37/1280),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/1280),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/1280),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00700_transform : affine00700=(NestedInteger.clearedAll 3 raw00700 (IntegerComputedClassCell.leftNumerator ![(37/1280),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/1280),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/1280),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00700_transform
theorem leaf00700_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00700=true := by decide +kernel
#print axioms leaf00700_sign
theorem leaf00700_log : RationalLog.accepts (35567599/2147483648) (-8806008073/4294967296) 6 8=true := by decide +kernel
#print axioms leaf00700_log
def leaf00700 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (218059590977/250000000000) (35567599/2147483648) (-8806008073/4294967296) 6 8 ![60,0,4] ![(37/1280),0,0] ![(3/6400),1,(1/16)] affine00700
theorem leaf00700_checked : FastNestedCellData.accepts 1 2 4 leaf00700=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (218059590977/250000000000) (35567599/2147483648) (-8806008073/4294967296) 6 8 ![60,0,4] ![(37/1280),0,0] ![(3/6400),1,(1/16)] 251405591723156472780189335552000000000000 7795801214522283112596019484131388817408 8937695860560142859948261376000000000000 raw00700 affine00700
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00700_raw leaf00700_rectangular
    leaf00700_transform leaf00700_sign leaf00700_log
#print axioms leaf00700_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
