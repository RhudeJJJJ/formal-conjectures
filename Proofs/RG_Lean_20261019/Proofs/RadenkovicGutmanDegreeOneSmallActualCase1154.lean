/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1154 : Family 8 := level8.get ⟨196,by decide⟩
def sourceMap1154 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap1154 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1154_checked : acceptsGraphIso
    (source (graph core1154) (root 8) 1 1) DegreeOneSmallSpectrum1613.graph sourceMap1154=true := by decide +kernel
theorem fusedMap1154_checked : acceptsGraphIso
    (fused (graph core1154) (root 8) 1 1) DegreeOneSmallSpectrum1009.graph fusedMap1154=true := by decide +kernel
theorem certified1154 : Certified (graph core1154) (root 8) 1 1 :=
  of_native_maps core1154 DegreeOneSmallSpectrum1613.graph DegreeOneSmallSpectrum1009.graph
    sourceMap1154 fusedMap1154 sourceMap1154_checked fusedMap1154_checked
    DegreeOneSmallComparisons.comparison1154
#print axioms sourceMap1154_checked
#print axioms fusedMap1154_checked
#print axioms certified1154
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
