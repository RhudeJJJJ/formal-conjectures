/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1587 : Family 9 := level9.get ⟨330,by decide⟩
def sourceMap1587 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (sourceLabel 9 0 0 v)
def fusedMap1587 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1587_checked : acceptsGraphIso
    (source (graph core1587) (root 9) 0 0) DegreeOneSmallSpectrum628.graph sourceMap1587=true := by decide +kernel
theorem fusedMap1587_checked : acceptsGraphIso
    (fused (graph core1587) (root 9) 0 0) DegreeOneSmallSpectrum630.graph fusedMap1587=true := by decide +kernel
theorem certified1587 : Certified (graph core1587) (root 9) 0 0 :=
  of_native_maps core1587 DegreeOneSmallSpectrum628.graph DegreeOneSmallSpectrum630.graph
    sourceMap1587 fusedMap1587 sourceMap1587_checked fusedMap1587_checked
    DegreeOneSmallComparisons.comparison1587
#print axioms sourceMap1587_checked
#print axioms fusedMap1587_checked
#print axioms certified1587
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
