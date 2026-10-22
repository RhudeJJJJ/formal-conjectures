/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00666 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 10436553851143624004391141376000000000000 3053836501799292407943309902146986573824 5271187071025997076355874816000000000000))
theorem leaf00666_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 10436553851143624004391141376000000000000 3053836501799292407943309902146986573824 5271187071025997076355874816000000000000 raw00666=true := by decide +kernel
#print axioms leaf00666_raw
theorem leaf00666_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00666=true := by decide +kernel
#print axioms leaf00666_rectangular
def affine00666 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00666 (IntegerComputedClassCell.leftNumerator ![(41/1600),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/1600),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/1600),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00666_transform : affine00666=(NestedInteger.clearedAll 3 raw00666 (IntegerComputedClassCell.leftNumerator ![(41/1600),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/1600),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/1600),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00666_transform
theorem leaf00666_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00666=true := by decide +kernel
#print axioms leaf00666_sign
theorem leaf00666_log : RationalLog.accepts (99467567/536870912) (-905124681/1073741824) 3 8=true := by decide +kernel
#print axioms leaf00666_log
def leaf00666 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (144836279791/250000000000) (99467567/536870912) (-905124681/1073741824) 3 8 ![60,0,4] ![(41/1600),0,(1/16)] ![(3/6400),1,(1/16)] affine00666
theorem leaf00666_checked : FastNestedCellData.accepts 1 2 4 leaf00666=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (144836279791/250000000000) (99467567/536870912) (-905124681/1073741824) 3 8 ![60,0,4] ![(41/1600),0,(1/16)] ![(3/6400),1,(1/16)] 10436553851143624004391141376000000000000 3053836501799292407943309902146986573824 5271187071025997076355874816000000000000 raw00666 affine00666
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00666_raw leaf00666_rectangular
    leaf00666_transform leaf00666_sign leaf00666_log
#print axioms leaf00666_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
