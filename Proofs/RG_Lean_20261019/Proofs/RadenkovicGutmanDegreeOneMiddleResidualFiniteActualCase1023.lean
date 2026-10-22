/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1023 : Family 10 := level10.get ⟨948,by decide⟩
def sourceMap1023 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1023 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1023_checked : acceptsGraphIso
    (source (graph core1023) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2326.graph sourceMap1023=true := by decide +kernel
theorem fusedMap1023_checked : acceptsGraphIso
    (fused (graph core1023) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1482.graph fusedMap1023=true := by decide +kernel
theorem certified1023 : Certified (graph core1023) (root 10) 2 2 :=
  of_native_maps core1023 DegreeOneMiddleResidualSpectrum2326.graph DegreeOneMiddleResidualSpectrum1482.graph
    sourceMap1023 fusedMap1023 sourceMap1023_checked fusedMap1023_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1023
#print axioms sourceMap1023_checked
#print axioms fusedMap1023_checked
#print axioms certified1023
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
