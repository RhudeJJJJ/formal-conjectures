/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1816 : Family 10 := level10.get ⟨60,by decide⟩
def sourceMap1816 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1816 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1816_checked : acceptsGraphIso
    (source (graph core1816) (root 10) 0 0) DegreeOneSmallSpectrum1104.graph sourceMap1816=true := by decide +kernel
theorem fusedMap1816_checked : acceptsGraphIso
    (fused (graph core1816) (root 10) 0 0) DegreeOneSmallSpectrum871.graph fusedMap1816=true := by decide +kernel
theorem certified1816 : Certified (graph core1816) (root 10) 0 0 :=
  of_native_maps core1816 DegreeOneSmallSpectrum1104.graph DegreeOneSmallSpectrum871.graph
    sourceMap1816 fusedMap1816 sourceMap1816_checked fusedMap1816_checked
    DegreeOneSmallComparisons.comparison1816
#print axioms sourceMap1816_checked
#print axioms fusedMap1816_checked
#print axioms certified1816
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
