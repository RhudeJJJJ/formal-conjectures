/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00436 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5982733038940413211154816434176000000000000 2949862231431791421629681714545610251567104 9095400593966900206637221412864000000000000))
theorem leaf00436_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5982733038940413211154816434176000000000000 2949862231431791421629681714545610251567104 9095400593966900206637221412864000000000000 raw00436=true := by decide +kernel
#print axioms leaf00436_raw
theorem leaf00436_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00436=true := by decide +kernel
#print axioms leaf00436_rectangular
def affine00436 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00436 (IntegerComputedClassCell.leftNumerator ![(71/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(71/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(71/6400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00436_transform : affine00436=(NestedInteger.clearedAll 3 raw00436 (IntegerComputedClassCell.leftNumerator ![(71/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(71/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(71/6400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00436_transform
theorem leaf00436_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00436=true := by decide +kernel
#print axioms leaf00436_sign
theorem leaf00436_log : RationalLog.accepts (1599070169/4294967296) (-2121760355/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00436_log
def leaf00436 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (324324607911/1000000000000) (1599070169/4294967296) (-2121760355/4294967296) 2 8 ![60,0,4] ![(71/6400),0,(1/16)] ![(1/6400),1,(1/16)] affine00436
theorem leaf00436_checked : FastNestedCellData.accepts 1 2 4 leaf00436=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (324324607911/1000000000000) (1599070169/4294967296) (-2121760355/4294967296) 2 8 ![60,0,4] ![(71/6400),0,(1/16)] ![(1/6400),1,(1/16)] 5982733038940413211154816434176000000000000 2949862231431791421629681714545610251567104 9095400593966900206637221412864000000000000 raw00436 affine00436
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00436_raw leaf00436_rectangular
    leaf00436_transform leaf00436_sign leaf00436_log
#print axioms leaf00436_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
