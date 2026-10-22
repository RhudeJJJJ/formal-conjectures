/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00631 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 99445526336502078158005495398400000000000 31403869702026930844286308335650988883968 58252911785814239814649852723200000000000))
theorem leaf00631_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 99445526336502078158005495398400000000000 31403869702026930844286308335650988883968 58252911785814239814649852723200000000000 raw00631=true := by decide +kernel
#print axioms leaf00631_raw
theorem leaf00631_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00631=true := by decide +kernel
#print axioms leaf00631_rectangular
def affine00631 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00631 (IntegerComputedClassCell.leftNumerator ![(143/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(143/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(143/6400),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00631_transform : affine00631=(NestedInteger.clearedAll 3 raw00631 (IntegerComputedClassCell.leftNumerator ![(143/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(143/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(143/6400),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00631_transform
theorem leaf00631_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00631=true := by decide +kernel
#print axioms leaf00631_sign
theorem leaf00631_log : RationalLog.accepts (881236083/4294967296) (-425167861/536870912) 3 8=true := by decide +kernel
#print axioms leaf00631_log
def leaf00631 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (53909527849/100000000000) (881236083/4294967296) (-425167861/536870912) 3 8 ![60,0,4] ![(143/6400),0,(1/16)] ![(3/6400),1,(1/16)] affine00631
theorem leaf00631_checked : FastNestedCellData.accepts 1 2 4 leaf00631=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (53909527849/100000000000) (881236083/4294967296) (-425167861/536870912) 3 8 ![60,0,4] ![(143/6400),0,(1/16)] ![(3/6400),1,(1/16)] 99445526336502078158005495398400000000000 31403869702026930844286308335650988883968 58252911785814239814649852723200000000000 raw00631 affine00631
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00631_raw leaf00631_rectangular
    leaf00631_transform leaf00631_sign leaf00631_log
#print axioms leaf00631_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
