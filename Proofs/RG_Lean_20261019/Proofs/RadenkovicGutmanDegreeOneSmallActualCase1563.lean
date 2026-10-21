/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1563 : Family 9 := level9.get ⟨293,by decide⟩
def sourceMap1563 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,9,10,11,5,6,7,8,3,4] (sourceLabel 9 0 0 v)
def fusedMap1563 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,7,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap1563_checked : acceptsGraphIso
    (source (graph core1563) (root 9) 0 0) DegreeOneSmallSpectrum677.graph sourceMap1563=true := by decide +kernel
theorem fusedMap1563_checked : acceptsGraphIso
    (fused (graph core1563) (root 9) 0 0) DegreeOneSmallSpectrum565.graph fusedMap1563=true := by decide +kernel
theorem certified1563 : Certified (graph core1563) (root 9) 0 0 :=
  of_native_maps core1563 DegreeOneSmallSpectrum677.graph DegreeOneSmallSpectrum565.graph
    sourceMap1563 fusedMap1563 sourceMap1563_checked fusedMap1563_checked
    DegreeOneSmallComparisons.comparison1563
#print axioms sourceMap1563_checked
#print axioms fusedMap1563_checked
#print axioms certified1563
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
