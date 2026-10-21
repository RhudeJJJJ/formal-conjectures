/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1459 : Family 9 := level9.get ⟨199,by decide⟩
def sourceMap1459 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1459 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1459_checked : acceptsGraphIso
    (source (graph core1459) (root 9) 0 0) DegreeOneSmallSpectrum750.graph sourceMap1459=true := by decide +kernel
theorem fusedMap1459_checked : acceptsGraphIso
    (fused (graph core1459) (root 9) 0 0) DegreeOneSmallSpectrum500.graph fusedMap1459=true := by decide +kernel
theorem certified1459 : Certified (graph core1459) (root 9) 0 0 :=
  of_native_maps core1459 DegreeOneSmallSpectrum750.graph DegreeOneSmallSpectrum500.graph
    sourceMap1459 fusedMap1459 sourceMap1459_checked fusedMap1459_checked
    DegreeOneSmallComparisons.comparison1459
#print axioms sourceMap1459_checked
#print axioms fusedMap1459_checked
#print axioms certified1459
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
