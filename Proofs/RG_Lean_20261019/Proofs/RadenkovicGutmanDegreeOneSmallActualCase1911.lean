/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1911 : Family 10 := level10.get ⟨197,by decide⟩
def sourceMap1911 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1911 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1911_checked : acceptsGraphIso
    (source (graph core1911) (root 10) 0 0) DegreeOneSmallSpectrum1024.graph sourceMap1911=true := by decide +kernel
theorem fusedMap1911_checked : acceptsGraphIso
    (fused (graph core1911) (root 10) 0 0) DegreeOneSmallSpectrum1027.graph fusedMap1911=true := by decide +kernel
theorem certified1911 : Certified (graph core1911) (root 10) 0 0 :=
  of_native_maps core1911 DegreeOneSmallSpectrum1024.graph DegreeOneSmallSpectrum1027.graph
    sourceMap1911 fusedMap1911 sourceMap1911_checked fusedMap1911_checked
    DegreeOneSmallComparisons.comparison1911
#print axioms sourceMap1911_checked
#print axioms fusedMap1911_checked
#print axioms certified1911
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
