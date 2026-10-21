/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1769 : Family 10 := level10.get ⟨2,by decide⟩
def sourceMap1769 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![4,3,2,1,0,7,8,9,10,11,12,5,6] (sourceLabel 10 0 0 v)
def fusedMap1769 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,7,0,1,2,3,4,5,6,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1769_checked : acceptsGraphIso
    (source (graph core1769) (root 10) 0 0) DegreeOneSmallSpectrum900.graph sourceMap1769=true := by decide +kernel
theorem fusedMap1769_checked : acceptsGraphIso
    (fused (graph core1769) (root 10) 0 0) DegreeOneSmallSpectrum857.graph fusedMap1769=true := by decide +kernel
theorem certified1769 : Certified (graph core1769) (root 10) 0 0 :=
  of_native_maps core1769 DegreeOneSmallSpectrum900.graph DegreeOneSmallSpectrum857.graph
    sourceMap1769 fusedMap1769 sourceMap1769_checked fusedMap1769_checked
    DegreeOneSmallComparisons.comparison1769
#print axioms sourceMap1769_checked
#print axioms fusedMap1769_checked
#print axioms certified1769
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
