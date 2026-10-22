/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00144 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1810117674405636445266967003136000000000000 11446128644104885356294318355306153771008 29161613181017270009947226112000000000000))
theorem leaf00144_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1810117674405636445266967003136000000000000 11446128644104885356294318355306153771008 29161613181017270009947226112000000000000 raw00144=true := by decide +kernel
#print axioms leaf00144_raw
theorem leaf00144_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00144=true := by decide +kernel
#print axioms leaf00144_rectangular
def affine00144 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00144 (IntegerComputedClassCell.leftNumerator ![(3/160),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/160),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/160),0,0] ![(1/1600),1,(1/4)]))
theorem leaf00144_transform : affine00144=(NestedInteger.clearedAll 3 raw00144 (IntegerComputedClassCell.leftNumerator ![(3/160),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/160),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/160),0,0] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00144_transform
theorem leaf00144_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00144=true := by decide +kernel
#print axioms leaf00144_sign
theorem leaf00144_log : RationalLog.accepts (9751791/2147483648) (-11584817887/4294967296) 8 8=true := by decide +kernel
#print axioms leaf00144_log
def leaf00144 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (392506703009/1000000000000) (9751791/2147483648) (-11584817887/4294967296) 8 8 ![52,0,4] ![(3/160),0,0] ![(1/1600),1,(1/4)] affine00144
theorem leaf00144_checked : FastNestedCellData.accepts 1 0 4 leaf00144=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (392506703009/1000000000000) (9751791/2147483648) (-11584817887/4294967296) 8 8 ![52,0,4] ![(3/160),0,0] ![(1/1600),1,(1/4)] 1810117674405636445266967003136000000000000 11446128644104885356294318355306153771008 29161613181017270009947226112000000000000 raw00144 affine00144
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00144_raw leaf00144_rectangular
    leaf00144_transform leaf00144_sign leaf00144_log
#print axioms leaf00144_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
