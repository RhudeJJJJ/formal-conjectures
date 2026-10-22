/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00431 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 236465950855146167672534518988800000000000 117530959609940031196987736325282926166016 366744307131163404408355343564800000000000))
theorem leaf00431_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 236465950855146167672534518988800000000000 117530959609940031196987736325282926166016 366744307131163404408355343564800000000000 raw00431=true := by decide +kernel
#print axioms leaf00431_raw
theorem leaf00431_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00431=true := by decide +kernel
#print axioms leaf00431_rectangular
def affine00431 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00431 (IntegerComputedClassCell.leftNumerator ![(7/640),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/640),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/640),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00431_transform : affine00431=(NestedInteger.clearedAll 3 raw00431 (IntegerComputedClassCell.leftNumerator ![(7/640),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/640),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/640),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00431_transform
theorem leaf00431_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00431=true := by decide +kernel
#print axioms leaf00431_sign
theorem leaf00431_log : RationalLog.accepts (1616644841/4294967296) (-1049143535/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00431_log
def leaf00431 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (64094224409/200000000000) (1616644841/4294967296) (-1049143535/2147483648) 2 8 ![60,0,4] ![(7/640),0,(1/16)] ![(1/6400),1,(1/16)] affine00431
theorem leaf00431_checked : FastNestedCellData.accepts 1 2 4 leaf00431=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (64094224409/200000000000) (1616644841/4294967296) (-1049143535/2147483648) 2 8 ![60,0,4] ![(7/640),0,(1/16)] ![(1/6400),1,(1/16)] 236465950855146167672534518988800000000000 117530959609940031196987736325282926166016 366744307131163404408355343564800000000000 raw00431 affine00431
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00431_raw leaf00431_rectangular
    leaf00431_transform leaf00431_sign leaf00431_log
#print axioms leaf00431_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
