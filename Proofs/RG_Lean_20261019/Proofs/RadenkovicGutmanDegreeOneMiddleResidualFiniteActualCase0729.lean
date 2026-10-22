/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0729 : Family 10 := level10.get ⟨350,by decide⟩
def sourceMap0729 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0729 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0729_checked : acceptsGraphIso
    (source (graph core0729) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1819.graph sourceMap0729=true := by decide +kernel
theorem fusedMap0729_checked : acceptsGraphIso
    (fused (graph core0729) (root 10) 2 2) DegreeTwoThreeSpectrum5622.graph fusedMap0729=true := by decide +kernel
theorem certified0729 : Certified (graph core0729) (root 10) 2 2 :=
  of_native_maps core0729 DegreeOneMiddleResidualSpectrum1819.graph DegreeTwoThreeSpectrum5622.graph
    sourceMap0729 fusedMap0729 sourceMap0729_checked fusedMap0729_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0729
#print axioms sourceMap0729_checked
#print axioms fusedMap0729_checked
#print axioms certified0729
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
