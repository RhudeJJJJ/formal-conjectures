/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00677 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 415998075555903875996884926464000000000000 199129002182231808090364855201820087156736 551877814578848219110859341824000000000000))
theorem leaf00677_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 415998075555903875996884926464000000000000 199129002182231808090364855201820087156736 551877814578848219110859341824000000000000 raw00677=true := by decide +kernel
#print axioms leaf00677_raw
theorem leaf00677_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00677=true := by decide +kernel
#print axioms leaf00677_rectangular
def affine00677 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00677 (IntegerComputedClassCell.leftNumerator ![(17/640),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/640),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/640),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00677_transform : affine00677=(NestedInteger.clearedAll 3 raw00677 (IntegerComputedClassCell.leftNumerator ![(17/640),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/640),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/640),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00677_transform
theorem leaf00677_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00677=true := by decide +kernel
#print axioms leaf00677_sign
theorem leaf00677_log : RationalLog.accepts (755391543/2147483648) (-2243724969/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00677_log
def leaf00677 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (180410406907/500000000000) (755391543/2147483648) (-2243724969/4294967296) 2 8 ![60,0,4] ![(17/640),0,(1/8)] ![(3/6400),1,(1/8)] affine00677
theorem leaf00677_checked : FastNestedCellData.accepts 1 2 4 leaf00677=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (180410406907/500000000000) (755391543/2147483648) (-2243724969/4294967296) 2 8 ![60,0,4] ![(17/640),0,(1/8)] ![(3/6400),1,(1/8)] 415998075555903875996884926464000000000000 199129002182231808090364855201820087156736 551877814578848219110859341824000000000000 raw00677 affine00677
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00677_raw leaf00677_rectangular
    leaf00677_transform leaf00677_sign leaf00677_log
#print axioms leaf00677_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
