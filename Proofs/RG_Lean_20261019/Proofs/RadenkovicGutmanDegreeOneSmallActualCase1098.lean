/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1098 : Family 8 := level8.get ⟨149,by decide⟩
def sourceMap1098 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap1098 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1098_checked : acceptsGraphIso
    (source (graph core1098) (root 8) 1 1) DegreeOneSmallSpectrum1922.graph sourceMap1098=true := by decide +kernel
theorem fusedMap1098_checked : acceptsGraphIso
    (fused (graph core1098) (root 8) 1 1) DegreeOneSmallSpectrum1398.graph fusedMap1098=true := by decide +kernel
theorem certified1098 : Certified (graph core1098) (root 8) 1 1 :=
  of_native_maps core1098 DegreeOneSmallSpectrum1922.graph DegreeOneSmallSpectrum1398.graph
    sourceMap1098 fusedMap1098 sourceMap1098_checked fusedMap1098_checked
    DegreeOneSmallComparisons.comparison1098
#print axioms sourceMap1098_checked
#print axioms fusedMap1098_checked
#print axioms certified1098
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
