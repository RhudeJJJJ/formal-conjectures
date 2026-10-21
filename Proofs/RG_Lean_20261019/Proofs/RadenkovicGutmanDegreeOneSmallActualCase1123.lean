/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1123 : Family 8 := level8.get ⟨166,by decide⟩
def sourceMap1123 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,8,9,10,4,5,6,7,2,3] (sourceLabel 8 0 0 v)
def fusedMap1123 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,4,5,6,7,8,9,10,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap1123_checked : acceptsGraphIso
    (source (graph core1123) (root 8) 0 0) DegreeOneSmallSpectrum271.graph sourceMap1123=true := by decide +kernel
theorem fusedMap1123_checked : acceptsGraphIso
    (fused (graph core1123) (root 8) 0 0) DegreeOneSmallSpectrum348.graph fusedMap1123=true := by decide +kernel
theorem certified1123 : Certified (graph core1123) (root 8) 0 0 :=
  of_native_maps core1123 DegreeOneSmallSpectrum271.graph DegreeOneSmallSpectrum348.graph
    sourceMap1123 fusedMap1123 sourceMap1123_checked fusedMap1123_checked
    DegreeOneSmallComparisons.comparison1123
#print axioms sourceMap1123_checked
#print axioms fusedMap1123_checked
#print axioms certified1123
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
