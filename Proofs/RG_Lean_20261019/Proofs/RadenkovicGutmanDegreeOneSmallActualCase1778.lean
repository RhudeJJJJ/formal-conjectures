/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1778 : Family 10 := level10.get ⟨12,by decide⟩
def sourceMap1778 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,7,0,1,2,3,4,5,6,11,12] (sourceLabel 10 0 0 v)
def fusedMap1778 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1778_checked : acceptsGraphIso
    (source (graph core1778) (root 10) 0 0) DegreeOneSmallSpectrum883.graph sourceMap1778=true := by decide +kernel
theorem fusedMap1778_checked : acceptsGraphIso
    (fused (graph core1778) (root 10) 0 0) DegreeOneSmallSpectrum887.graph fusedMap1778=true := by decide +kernel
theorem certified1778 : Certified (graph core1778) (root 10) 0 0 :=
  of_native_maps core1778 DegreeOneSmallSpectrum883.graph DegreeOneSmallSpectrum887.graph
    sourceMap1778 fusedMap1778 sourceMap1778_checked fusedMap1778_checked
    DegreeOneSmallComparisons.comparison1778
#print axioms sourceMap1778_checked
#print axioms fusedMap1778_checked
#print axioms certified1778
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
