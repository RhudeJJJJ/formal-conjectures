/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00800 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 10150175752296910788982367846400000000000 670682325867786664089224417902055129088 761803632885596832031519539200000000000))
theorem leaf00800_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 10150175752296910788982367846400000000000 670682325867786664089224417902055129088 761803632885596832031519539200000000000 raw00800=true := by decide +kernel
#print axioms leaf00800_raw
theorem leaf00800_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00800=true := by decide +kernel
#print axioms leaf00800_rectangular
def affine00800 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00800 (IntegerComputedClassCell.leftNumerator ![(17/400),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/400),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/400),0,0] ![(3/3200),1,(1/16)]))
theorem leaf00800_transform : affine00800=(NestedInteger.clearedAll 3 raw00800 (IntegerComputedClassCell.leftNumerator ![(17/400),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/400),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/400),0,0] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00800_transform
theorem leaf00800_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00800=true := by decide +kernel
#print axioms leaf00800_sign
theorem leaf00800_log : RationalLog.accepts (75461569/2147483648) (-7190695697/4294967296) 5 8=true := by decide +kernel
#print axioms leaf00800_log
def leaf00800 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (44019370407/50000000000) (75461569/2147483648) (-7190695697/4294967296) 5 8 ![60,0,4] ![(17/400),0,0] ![(3/3200),1,(1/16)] affine00800
theorem leaf00800_checked : FastNestedCellData.accepts 1 2 4 leaf00800=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (44019370407/50000000000) (75461569/2147483648) (-7190695697/4294967296) 5 8 ![60,0,4] ![(17/400),0,0] ![(3/3200),1,(1/16)] 10150175752296910788982367846400000000000 670682325867786664089224417902055129088 761803632885596832031519539200000000000 raw00800 affine00800
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00800_raw leaf00800_rectangular
    leaf00800_transform leaf00800_sign leaf00800_log
#print axioms leaf00800_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
