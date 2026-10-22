/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1020 : Family 10 := level10.get ⟨941,by decide⟩
def sourceMap1020 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1020 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1020_checked : acceptsGraphIso
    (source (graph core1020) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2323.graph sourceMap1020=true := by decide +kernel
theorem fusedMap1020_checked : acceptsGraphIso
    (fused (graph core1020) (root 10) 2 2) DegreeTwoThreeSpectrum5840.graph fusedMap1020=true := by decide +kernel
theorem certified1020 : Certified (graph core1020) (root 10) 2 2 :=
  of_native_maps core1020 DegreeOneMiddleResidualSpectrum2323.graph DegreeTwoThreeSpectrum5840.graph
    sourceMap1020 fusedMap1020 sourceMap1020_checked fusedMap1020_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1020
#print axioms sourceMap1020_checked
#print axioms fusedMap1020_checked
#print axioms certified1020
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
