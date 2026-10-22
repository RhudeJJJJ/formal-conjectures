/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00352 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 150344390644245206062979874816000000000000 112406502923115079611612833123880482635776 861993413404894296944238657536000000000000))
theorem leaf00352_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 150344390644245206062979874816000000000000 112406502923115079611612833123880482635776 861993413404894296944238657536000000000000 raw00352=true := by decide +kernel
#print axioms leaf00352_raw
theorem leaf00352_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00352=true := by decide +kernel
#print axioms leaf00352_rectangular
def affine00352 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00352 (IntegerComputedClassCell.leftNumerator ![(27/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(27/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(27/3200),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00352_transform : affine00352=(NestedInteger.clearedAll 3 raw00352 (IntegerComputedClassCell.leftNumerator ![(27/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(27/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(27/3200),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00352_transform
theorem leaf00352_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00352=true := by decide +kernel
#print axioms leaf00352_sign
theorem leaf00352_log : RationalLog.accepts (1420367683/2147483648) (-443864477/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00352_log
def leaf00352 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (65201485983/500000000000) (1420367683/2147483648) (-443864477/2147483648) 1 8 ![60,0,4] ![(27/3200),0,(1/8)] ![(1/6400),1,(1/8)] affine00352
theorem leaf00352_checked : FastNestedCellData.accepts 1 2 4 leaf00352=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (65201485983/500000000000) (1420367683/2147483648) (-443864477/2147483648) 1 8 ![60,0,4] ![(27/3200),0,(1/8)] ![(1/6400),1,(1/8)] 150344390644245206062979874816000000000000 112406502923115079611612833123880482635776 861993413404894296944238657536000000000000 raw00352 affine00352
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00352_raw leaf00352_rectangular
    leaf00352_transform leaf00352_sign leaf00352_log
#print axioms leaf00352_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
