/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1815 : Family 10 := level10.get ⟨58,by decide⟩
def sourceMap1815 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap1815 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1815_checked : acceptsGraphIso
    (source (graph core1815) (root 10) 0 0) DegreeOneSmallSpectrum1063.graph sourceMap1815=true := by decide +kernel
theorem fusedMap1815_checked : acceptsGraphIso
    (fused (graph core1815) (root 10) 0 0) DegreeOneSmallSpectrum868.graph fusedMap1815=true := by decide +kernel
theorem certified1815 : Certified (graph core1815) (root 10) 0 0 :=
  of_native_maps core1815 DegreeOneSmallSpectrum1063.graph DegreeOneSmallSpectrum868.graph
    sourceMap1815 fusedMap1815 sourceMap1815_checked fusedMap1815_checked
    DegreeOneSmallComparisons.comparison1815
#print axioms sourceMap1815_checked
#print axioms fusedMap1815_checked
#print axioms certified1815
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
