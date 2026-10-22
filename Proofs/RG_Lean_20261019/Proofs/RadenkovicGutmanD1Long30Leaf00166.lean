/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00166 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2098004505197956299758067777536000000000000 1620391544219186640217594167127249526980608 14247323130792801914712225742848000000000000))
theorem leaf00166_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2098004505197956299758067777536000000000000 1620391544219186640217594167127249526980608 14247323130792801914712225742848000000000000 raw00166=true := by decide +kernel
#print axioms leaf00166_raw
theorem leaf00166_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00166=true := by decide +kernel
#print axioms leaf00166_rectangular
def affine00166 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00166 (IntegerComputedClassCell.leftNumerator ![(23/6400),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/6400),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/6400),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00166_transform : affine00166=(NestedInteger.clearedAll 3 raw00166 (IntegerComputedClassCell.leftNumerator ![(23/6400),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/6400),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/6400),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00166_transform
theorem leaf00166_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00166=true := by decide +kernel
#print axioms leaf00166_sign
theorem leaf00166_log : RationalLog.accepts (2978463653/4294967296) (-786057061/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00166_log
def leaf00166 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (113733052121/1000000000000) (2978463653/4294967296) (-786057061/4294967296) 1 8 ![60,0,4] ![(23/6400),0,(1/16)] ![(3/32000),1,(1/16)] affine00166
theorem leaf00166_checked : FastNestedCellData.accepts 1 2 4 leaf00166=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (113733052121/1000000000000) (2978463653/4294967296) (-786057061/4294967296) 1 8 ![60,0,4] ![(23/6400),0,(1/16)] ![(3/32000),1,(1/16)] 2098004505197956299758067777536000000000000 1620391544219186640217594167127249526980608 14247323130792801914712225742848000000000000 raw00166 affine00166
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00166_raw leaf00166_rectangular
    leaf00166_transform leaf00166_sign leaf00166_log
#print axioms leaf00166_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
