/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1465 : Family 9 := level9.get ⟨202,by decide⟩
def sourceMap1465 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1465 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1465_checked : acceptsGraphIso
    (source (graph core1465) (root 9) 0 0) DegreeOneSmallSpectrum734.graph sourceMap1465=true := by decide +kernel
theorem fusedMap1465_checked : acceptsGraphIso
    (fused (graph core1465) (root 9) 0 0) DegreeOneSmallSpectrum504.graph fusedMap1465=true := by decide +kernel
theorem certified1465 : Certified (graph core1465) (root 9) 0 0 :=
  of_native_maps core1465 DegreeOneSmallSpectrum734.graph DegreeOneSmallSpectrum504.graph
    sourceMap1465 fusedMap1465 sourceMap1465_checked fusedMap1465_checked
    DegreeOneSmallComparisons.comparison1465
#print axioms sourceMap1465_checked
#print axioms fusedMap1465_checked
#print axioms certified1465
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
