/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00279 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 12809394090534050666056823865344000000000000 1311278813891597048169946809453607762526208 1888366031849303871108270784512000000000000))
theorem leaf00279_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 12809394090534050666056823865344000000000000 1311278813891597048169946809453607762526208 1888366031849303871108270784512000000000000 raw00279=true := by decide +kernel
#print axioms leaf00279_raw
theorem leaf00279_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00279=true := by decide +kernel
#print axioms leaf00279_rectangular
def affine00279 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00279 (IntegerComputedClassCell.leftNumerator ![(41/640),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/640),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/640),0,0] ![(1/640),1,(1/4)]))
theorem leaf00279_transform : affine00279=(NestedInteger.clearedAll 3 raw00279 (IntegerComputedClassCell.leftNumerator ![(41/640),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/640),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/640),0,0] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00279_transform
theorem leaf00279_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00279=true := by decide +kernel
#print axioms leaf00279_sign
theorem leaf00279_log : RationalLog.accepts (259484083/4294967296) (-6026921317/4294967296) 5 8=true := by decide +kernel
#print axioms leaf00279_log
def leaf00279 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (694398645059/1000000000000) (259484083/4294967296) (-6026921317/4294967296) 5 8 ![52,0,4] ![(41/640),0,0] ![(1/640),1,(1/4)] affine00279
theorem leaf00279_checked : FastNestedCellData.accepts 1 0 4 leaf00279=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (694398645059/1000000000000) (259484083/4294967296) (-6026921317/4294967296) 5 8 ![52,0,4] ![(41/640),0,0] ![(1/640),1,(1/4)] 12809394090534050666056823865344000000000000 1311278813891597048169946809453607762526208 1888366031849303871108270784512000000000000 raw00279 affine00279
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00279_raw leaf00279_rectangular
    leaf00279_transform leaf00279_sign leaf00279_log
#print axioms leaf00279_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
