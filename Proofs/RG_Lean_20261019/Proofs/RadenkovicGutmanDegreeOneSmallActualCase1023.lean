/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1023 : Family 8 := level8.get ⟨110,by decide⟩
def sourceMap1023 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (sourceLabel 8 0 0 v)
def fusedMap1023 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap1023_checked : acceptsGraphIso
    (source (graph core1023) (root 8) 0 0) DegreeOneSmallSpectrum276.graph sourceMap1023=true := by decide +kernel
theorem fusedMap1023_checked : acceptsGraphIso
    (fused (graph core1023) (root 8) 0 0) DegreeOneSmallSpectrum281.graph fusedMap1023=true := by decide +kernel
theorem certified1023 : Certified (graph core1023) (root 8) 0 0 :=
  of_native_maps core1023 DegreeOneSmallSpectrum276.graph DegreeOneSmallSpectrum281.graph
    sourceMap1023 fusedMap1023 sourceMap1023_checked fusedMap1023_checked
    DegreeOneSmallComparisons.comparison1023
#print axioms sourceMap1023_checked
#print axioms fusedMap1023_checked
#print axioms certified1023
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
