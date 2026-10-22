/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0087 : Family 8 := level8.get ⟨36,by decide⟩
def sourceMap0087 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0087 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0087_checked : acceptsGraphIso
    (source (graph core0087) (root 8) 2 2) DegreeOneMiddleResidualSpectrum274.graph sourceMap0087=true := by decide +kernel
theorem fusedMap0087_checked : acceptsGraphIso
    (fused (graph core0087) (root 8) 2 2) DegreeTwoThreeSpectrum2316.graph fusedMap0087=true := by decide +kernel
theorem certified0087 : Certified (graph core0087) (root 8) 2 2 :=
  of_native_maps core0087 DegreeOneMiddleResidualSpectrum274.graph DegreeTwoThreeSpectrum2316.graph
    sourceMap0087 fusedMap0087 sourceMap0087_checked fusedMap0087_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0087
#print axioms sourceMap0087_checked
#print axioms fusedMap0087_checked
#print axioms certified0087
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
