/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1699 : Family 9 := level9.get ⟨464,by decide⟩
def sourceMap1699 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,7,2,3] (sourceLabel 9 0 0 v)
def fusedMap1699 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap1699_checked : acceptsGraphIso
    (source (graph core1699) (root 9) 0 0) DegreeOneSmallSpectrum686.graph sourceMap1699=true := by decide +kernel
theorem fusedMap1699_checked : acceptsGraphIso
    (fused (graph core1699) (root 9) 0 0) DegreeOneSmallSpectrum819.graph fusedMap1699=true := by decide +kernel
theorem certified1699 : Certified (graph core1699) (root 9) 0 0 :=
  of_native_maps core1699 DegreeOneSmallSpectrum686.graph DegreeOneSmallSpectrum819.graph
    sourceMap1699 fusedMap1699 sourceMap1699_checked fusedMap1699_checked
    DegreeOneSmallComparisons.comparison1699
#print axioms sourceMap1699_checked
#print axioms fusedMap1699_checked
#print axioms certified1699
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
