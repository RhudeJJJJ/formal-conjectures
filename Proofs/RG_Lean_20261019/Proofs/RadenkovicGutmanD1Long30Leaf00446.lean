/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00446 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 382720321714765562029073760256000000000000 185734143420448384617997815759354311213056 559512719705434286725871435776000000000000))
theorem leaf00446_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 382720321714765562029073760256000000000000 185734143420448384617997815759354311213056 559512719705434286725871435776000000000000 raw00446=true := by decide +kernel
#print axioms leaf00446_raw
theorem leaf00446_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00446=true := by decide +kernel
#print axioms leaf00446_rectangular
def affine00446 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00446 (IntegerComputedClassCell.leftNumerator ![(73/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(73/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(73/6400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00446_transform : affine00446=(NestedInteger.clearedAll 3 raw00446 (IntegerComputedClassCell.leftNumerator ![(73/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(73/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(73/6400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00446_transform
theorem leaf00446_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00446=true := by decide +kernel
#print axioms leaf00446_sign
theorem leaf00446_log : RationalLog.accepts (782437933/2147483648) (-1084089981/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00446_log
def leaf00446 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (165978481703/500000000000) (782437933/2147483648) (-1084089981/2147483648) 2 8 ![60,0,4] ![(73/6400),0,(1/16)] ![(1/6400),1,(1/16)] affine00446
theorem leaf00446_checked : FastNestedCellData.accepts 1 2 4 leaf00446=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (165978481703/500000000000) (782437933/2147483648) (-1084089981/2147483648) 2 8 ![60,0,4] ![(73/6400),0,(1/16)] ![(1/6400),1,(1/16)] 382720321714765562029073760256000000000000 185734143420448384617997815759354311213056 559512719705434286725871435776000000000000 raw00446 affine00446
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00446_raw leaf00446_rectangular
    leaf00446_transform leaf00446_sign leaf00446_log
#print axioms leaf00446_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
