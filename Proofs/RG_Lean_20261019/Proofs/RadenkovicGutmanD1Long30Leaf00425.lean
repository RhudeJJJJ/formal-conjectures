/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00425 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3196371630090358646556466348032000000000000 12294406957007921282379623103966706925568 17738220466838218345646391296000000000000))
theorem leaf00425_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3196371630090358646556466348032000000000000 12294406957007921282379623103966706925568 17738220466838218345646391296000000000000 raw00425=true := by decide +kernel
#print axioms leaf00425_raw
theorem leaf00425_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00425=true := by decide +kernel
#print axioms leaf00425_rectangular
def affine00425 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00425 (IntegerComputedClassCell.leftNumerator ![(69/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(69/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(69/6400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00425_transform : affine00425=(NestedInteger.clearedAll 3 raw00425 (IntegerComputedClassCell.leftNumerator ![(69/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(69/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(69/6400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00425_transform
theorem leaf00425_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00425=true := by decide +kernel
#print axioms leaf00425_sign
theorem leaf00425_log : RationalLog.accepts (4878619/2147483648) (-6536070493/2147483648) 9 8=true := by decide +kernel
#print axioms leaf00425_log
def leaf00425 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (693102613083/1000000000000) (4878619/2147483648) (-6536070493/2147483648) 9 8 ![60,0,4] ![(69/6400),0,0] ![(1/6400),1,(1/16)] affine00425
theorem leaf00425_checked : FastNestedCellData.accepts 1 2 4 leaf00425=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (693102613083/1000000000000) (4878619/2147483648) (-6536070493/2147483648) 9 8 ![60,0,4] ![(69/6400),0,0] ![(1/6400),1,(1/16)] 3196371630090358646556466348032000000000000 12294406957007921282379623103966706925568 17738220466838218345646391296000000000000 raw00425 affine00425
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00425_raw leaf00425_rectangular
    leaf00425_transform leaf00425_sign leaf00425_log
#print axioms leaf00425_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
