/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1114 : Family 8 := level8.get ⟨161,by decide⟩
def sourceMap1114 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap1114 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1114_checked : acceptsGraphIso
    (source (graph core1114) (root 8) 1 1) DegreeOneSmallSpectrum1926.graph sourceMap1114=true := by decide +kernel
theorem fusedMap1114_checked : acceptsGraphIso
    (fused (graph core1114) (root 8) 1 1) DegreeOneSmallSpectrum1459.graph fusedMap1114=true := by decide +kernel
theorem certified1114 : Certified (graph core1114) (root 8) 1 1 :=
  of_native_maps core1114 DegreeOneSmallSpectrum1926.graph DegreeOneSmallSpectrum1459.graph
    sourceMap1114 fusedMap1114 sourceMap1114_checked fusedMap1114_checked
    DegreeOneSmallComparisons.comparison1114
#print axioms sourceMap1114_checked
#print axioms fusedMap1114_checked
#print axioms certified1114
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
