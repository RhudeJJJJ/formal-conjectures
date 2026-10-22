/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00005 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1441078456664307456798621696000000000000 1420997035986827318930516165173450899456 284213887383342647803992080384000000000000))
theorem leaf00005_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1441078456664307456798621696000000000000 1420997035986827318930516165173450899456 284213887383342647803992080384000000000000 raw00005=true := by decide +kernel
#print axioms leaf00005_raw
theorem leaf00005_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00005=true := by decide +kernel
#print axioms leaf00005_rectangular
def affine00005 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00005 (IntegerComputedClassCell.leftNumerator ![(1/800),0,(1/2)] ![(1/4000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/800),0,(1/2)] ![(1/4000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/800),0,(1/2)] ![(1/4000),1,(1/2)]))
theorem leaf00005_transform : affine00005=(NestedInteger.clearedAll 3 raw00005 (IntegerComputedClassCell.leftNumerator ![(1/800),0,(1/2)] ![(1/4000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/800),0,(1/2)] ![(1/4000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/800),0,(1/2)] ![(1/4000),1,(1/2)])) := by decide +kernel
#print axioms leaf00005_transform
theorem leaf00005_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00005=true := by decide +kernel
#print axioms leaf00005_sign
theorem leaf00005_log : RationalLog.accepts (526755973/536870912) (-40845791/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00005_log
def leaf00005 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (4999745259/1000000000000) (526755973/536870912) (-40845791/4294967296) 1 8 ![52,0,4] ![(1/800),0,(1/2)] ![(1/4000),1,(1/2)] affine00005
theorem leaf00005_checked : FastNestedCellData.accepts 1 0 4 leaf00005=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (4999745259/1000000000000) (526755973/536870912) (-40845791/4294967296) 1 8 ![52,0,4] ![(1/800),0,(1/2)] ![(1/4000),1,(1/2)] 1441078456664307456798621696000000000000 1420997035986827318930516165173450899456 284213887383342647803992080384000000000000 raw00005 affine00005
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00005_raw leaf00005_rectangular
    leaf00005_transform leaf00005_sign leaf00005_log
#print axioms leaf00005_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
