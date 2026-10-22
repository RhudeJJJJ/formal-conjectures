/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00166 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 30442366114186401270079978209280000000000 21369753679628489503817014156549169348608 129491372506231723464721432576000000000000))
theorem leaf00166_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 30442366114186401270079978209280000000000 21369753679628489503817014156549169348608 129491372506231723464721432576000000000000 raw00166=true := by decide +kernel
#print axioms leaf00166_raw
theorem leaf00166_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00166=true := by decide +kernel
#print axioms leaf00166_rectangular
def affine00166 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00166 (IntegerComputedClassCell.leftNumerator ![(143/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(143/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(143/6400),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00166_transform : affine00166=(NestedInteger.clearedAll 3 raw00166 (IntegerComputedClassCell.leftNumerator ![(143/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(143/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(143/6400),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00166_transform
theorem leaf00166_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00166=true := by decide +kernel
#print axioms leaf00166_sign
theorem leaf00166_log : RationalLog.accepts (1293940975/2147483648) (-271981057/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00166_log
def leaf00166 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (165028397383/1000000000000) (1293940975/2147483648) (-271981057/1073741824) 1 8 ![52,0,4] ![(143/6400),0,(1/4)] ![(3/6400),1,(1/4)] affine00166
theorem leaf00166_checked : FastNestedCellData.accepts 1 0 4 leaf00166=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (165028397383/1000000000000) (1293940975/2147483648) (-271981057/1073741824) 1 8 ![52,0,4] ![(143/6400),0,(1/4)] ![(3/6400),1,(1/4)] 30442366114186401270079978209280000000000 21369753679628489503817014156549169348608 129491372506231723464721432576000000000000 raw00166 affine00166
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00166_raw leaf00166_rectangular
    leaf00166_transform leaf00166_sign leaf00166_log
#print axioms leaf00166_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
