/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00269 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 398652113884948600787725975552000000000000 378860319238202236820010455522635323277312 17530922589533723411777843101696000000000000))
theorem leaf00269_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 398652113884948600787725975552000000000000 378860319238202236820010455522635323277312 17530922589533723411777843101696000000000000 raw00269=true := by decide +kernel
#print axioms leaf00269_raw
theorem leaf00269_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00269=true := by decide +kernel
#print axioms leaf00269_rectangular
def affine00269 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00269 (IntegerComputedClassCell.leftNumerator ![(37/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/6400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00269_transform : affine00269=(NestedInteger.clearedAll 3 raw00269 (IntegerComputedClassCell.leftNumerator ![(37/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/6400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00269_transform
theorem leaf00269_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00269=true := by decide +kernel
#print axioms leaf00269_sign
theorem leaf00269_log : RationalLog.accepts (3995391683/4294967296) (-155268093/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00269_log
def leaf00269 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (21610974397/1000000000000) (3995391683/4294967296) (-155268093/4294967296) 1 8 ![60,0,4] ![(37/6400),0,(1/2)] ![(1/6400),1,(1/2)] affine00269
theorem leaf00269_checked : FastNestedCellData.accepts 1 2 4 leaf00269=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (21610974397/1000000000000) (3995391683/4294967296) (-155268093/4294967296) 1 8 ![60,0,4] ![(37/6400),0,(1/2)] ![(1/6400),1,(1/2)] 398652113884948600787725975552000000000000 378860319238202236820010455522635323277312 17530922589533723411777843101696000000000000 raw00269 affine00269
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00269_raw leaf00269_rectangular
    leaf00269_transform leaf00269_sign leaf00269_log
#print axioms leaf00269_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
