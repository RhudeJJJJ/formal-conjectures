/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00402 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7071374585216027665687065395200000000000 5040829232814334070000363053650530009088 32874402867656518876945553817600000000000))
theorem leaf00402_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7071374585216027665687065395200000000000 5040829232814334070000363053650530009088 32874402867656518876945553817600000000000 raw00402=true := by decide +kernel
#print axioms leaf00402_raw
theorem leaf00402_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00402=true := by decide +kernel
#print axioms leaf00402_rectangular
def affine00402 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00402 (IntegerComputedClassCell.leftNumerator ![(1/100),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/100),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/100),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00402_transform : affine00402=(NestedInteger.clearedAll 3 raw00402 (IntegerComputedClassCell.leftNumerator ![(1/100),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/100),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/100),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00402_transform
theorem leaf00402_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00402=true := by decide +kernel
#print axioms leaf00402_sign
theorem leaf00402_log : RationalLog.accepts (663654687/1073741824) (-516623267/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00402_log
def leaf00402 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (30667198751/200000000000) (663654687/1073741824) (-516623267/2147483648) 1 8 ![60,0,4] ![(1/100),0,(1/8)] ![(1/6400),1,(1/8)] affine00402
theorem leaf00402_checked : FastNestedCellData.accepts 1 2 4 leaf00402=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (30667198751/200000000000) (663654687/1073741824) (-516623267/2147483648) 1 8 ![60,0,4] ![(1/100),0,(1/8)] ![(1/6400),1,(1/8)] 7071374585216027665687065395200000000000 5040829232814334070000363053650530009088 32874402867656518876945553817600000000000 raw00402 affine00402
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00402_raw leaf00402_rectangular
    leaf00402_transform leaf00402_sign leaf00402_log
#print axioms leaf00402_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
