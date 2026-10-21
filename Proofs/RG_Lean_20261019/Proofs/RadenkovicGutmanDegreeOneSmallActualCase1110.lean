/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1110 : Family 8 := level8.get ⟨153,by decide⟩
def sourceMap1110 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap1110 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1110_checked : acceptsGraphIso
    (source (graph core1110) (root 8) 1 1) DegreeOneSmallSpectrum1925.graph sourceMap1110=true := by decide +kernel
theorem fusedMap1110_checked : acceptsGraphIso
    (fused (graph core1110) (root 8) 1 1) DegreeOneSmallSpectrum1418.graph fusedMap1110=true := by decide +kernel
theorem certified1110 : Certified (graph core1110) (root 8) 1 1 :=
  of_native_maps core1110 DegreeOneSmallSpectrum1925.graph DegreeOneSmallSpectrum1418.graph
    sourceMap1110 fusedMap1110 sourceMap1110_checked fusedMap1110_checked
    DegreeOneSmallComparisons.comparison1110
#print axioms sourceMap1110_checked
#print axioms fusedMap1110_checked
#print axioms certified1110
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
