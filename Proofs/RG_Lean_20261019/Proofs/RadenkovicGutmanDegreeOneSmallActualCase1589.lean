/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1589 : Family 9 := level9.get ⟨331,by decide⟩
def sourceMap1589 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (sourceLabel 9 0 0 v)
def fusedMap1589 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1589_checked : acceptsGraphIso
    (source (graph core1589) (root 9) 0 0) DegreeOneSmallSpectrum633.graph sourceMap1589=true := by decide +kernel
theorem fusedMap1589_checked : acceptsGraphIso
    (fused (graph core1589) (root 9) 0 0) DegreeOneSmallSpectrum635.graph fusedMap1589=true := by decide +kernel
theorem certified1589 : Certified (graph core1589) (root 9) 0 0 :=
  of_native_maps core1589 DegreeOneSmallSpectrum633.graph DegreeOneSmallSpectrum635.graph
    sourceMap1589 fusedMap1589 sourceMap1589_checked fusedMap1589_checked
    DegreeOneSmallComparisons.comparison1589
#print axioms sourceMap1589_checked
#print axioms fusedMap1589_checked
#print axioms certified1589
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
