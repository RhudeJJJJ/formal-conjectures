/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00380 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 52125490476275160283441266688000000000000 56554368806008917061237565316876734562304 178697182456499629392966713344000000000000))
theorem leaf00380_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 52125490476275160283441266688000000000000 56554368806008917061237565316876734562304 178697182456499629392966713344000000000000 raw00380=true := by decide +kernel
#print axioms leaf00380_raw
theorem leaf00380_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00380=true := by decide +kernel
#print axioms leaf00380_rectangular
def affine00380 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00380 (IntegerComputedClassCell.leftNumerator ![(31/80),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/80),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/80),0,(1/2)] ![(3/80),1,(1/2)]))
theorem leaf00380_transform : affine00380=(NestedInteger.clearedAll 3 raw00380 (IntegerComputedClassCell.leftNumerator ![(31/80),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/80),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/80),0,(1/2)] ![(3/80),1,(1/2)])) := by decide +kernel
#print axioms leaf00380_transform
theorem leaf00380_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00380=true := by decide +kernel
#print axioms leaf00380_sign
theorem leaf00380_log : RationalLog.accepts (884914037/1073741824) (-207677097/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00380_log
def leaf00380 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (316481592091/1000000000000) (884914037/1073741824) (-207677097/2147483648) 1 8 ![52,0,4] ![(31/80),0,(1/2)] ![(3/80),1,(1/2)] affine00380
theorem leaf00380_checked : FastNestedCellData.accepts 1 0 4 leaf00380=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (316481592091/1000000000000) (884914037/1073741824) (-207677097/2147483648) 1 8 ![52,0,4] ![(31/80),0,(1/2)] ![(3/80),1,(1/2)] 52125490476275160283441266688000000000000 56554368806008917061237565316876734562304 178697182456499629392966713344000000000000 raw00380 affine00380
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00380_raw leaf00380_rectangular
    leaf00380_transform leaf00380_sign leaf00380_log
#print axioms leaf00380_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
