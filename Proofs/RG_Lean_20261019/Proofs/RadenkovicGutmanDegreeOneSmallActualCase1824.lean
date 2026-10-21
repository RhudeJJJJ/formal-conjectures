/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1824 : Family 10 := level10.get ⟨69,by decide⟩
def sourceMap1824 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap1824 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1824_checked : acceptsGraphIso
    (source (graph core1824) (root 10) 0 0) DegreeOneSmallSpectrum1228.graph sourceMap1824=true := by decide +kernel
theorem fusedMap1824_checked : acceptsGraphIso
    (fused (graph core1824) (root 10) 0 0) DegreeOneSmallSpectrum882.graph fusedMap1824=true := by decide +kernel
theorem certified1824 : Certified (graph core1824) (root 10) 0 0 :=
  of_native_maps core1824 DegreeOneSmallSpectrum1228.graph DegreeOneSmallSpectrum882.graph
    sourceMap1824 fusedMap1824 sourceMap1824_checked fusedMap1824_checked
    DegreeOneSmallComparisons.comparison1824
#print axioms sourceMap1824_checked
#print axioms fusedMap1824_checked
#print axioms certified1824
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
