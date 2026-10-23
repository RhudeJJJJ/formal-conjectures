/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1LCMInverseStageInner
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages
def source00 : NestedInteger.Poly 3 := inner01753
def segment00 : NestedInteger.Poly 3 := source00.take 12
def source01 : NestedInteger.Poly 3 := source00.drop 12
def segment01 : NestedInteger.Poly 3 := source01.take 12
def source02 : NestedInteger.Poly 3 := source01.drop 12
def segment02 : NestedInteger.Poly 3 := source02.take 12
def source03 : NestedInteger.Poly 3 := source02.drop 12
def segment03 : NestedInteger.Poly 3 := source03.take 12
def source04 : NestedInteger.Poly 3 := source03.drop 12
def segment04 : NestedInteger.Poly 3 := source04.take 12
def source05 : NestedInteger.Poly 3 := source04.drop 12
def segment05 : NestedInteger.Poly 3 := source05.take 12
def source06 : NestedInteger.Poly 3 := source05.drop 12
def segment06 : NestedInteger.Poly 3 := source06.take 12
def source07 : NestedInteger.Poly 3 := source06.drop 12
def segment07 : NestedInteger.Poly 3 := source07.take 12
#print axioms source07
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
