/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1134 : Family 8 := level8.get ⟨171,by decide⟩
def sourceMap1134 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap1134 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1134_checked : acceptsGraphIso
    (source (graph core1134) (root 8) 1 1) DegreeOneSmallSpectrum1931.graph sourceMap1134=true := by decide +kernel
theorem fusedMap1134_checked : acceptsGraphIso
    (fused (graph core1134) (root 8) 1 1) DegreeOneSmallSpectrum1494.graph fusedMap1134=true := by decide +kernel
theorem certified1134 : Certified (graph core1134) (root 8) 1 1 :=
  of_native_maps core1134 DegreeOneSmallSpectrum1931.graph DegreeOneSmallSpectrum1494.graph
    sourceMap1134 fusedMap1134 sourceMap1134_checked fusedMap1134_checked
    DegreeOneSmallComparisons.comparison1134
#print axioms sourceMap1134_checked
#print axioms fusedMap1134_checked
#print axioms certified1134
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
