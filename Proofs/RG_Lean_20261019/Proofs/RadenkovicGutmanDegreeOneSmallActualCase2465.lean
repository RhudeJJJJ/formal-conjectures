/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2465 : Family 10 := level10.get ⟨1545,by decide⟩
def sourceMap2465 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (sourceLabel 10 0 0 v)
def fusedMap2465 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2465_checked : acceptsGraphIso
    (source (graph core2465) (root 10) 0 0) DegreeOneSmallSpectrum2000.graph sourceMap2465=true := by decide +kernel
theorem fusedMap2465_checked : acceptsGraphIso
    (fused (graph core2465) (root 10) 0 0) DegreeOneSmallSpectrum1559.graph fusedMap2465=true := by decide +kernel
theorem certified2465 : Certified (graph core2465) (root 10) 0 0 :=
  of_native_maps core2465 DegreeOneSmallSpectrum2000.graph DegreeOneSmallSpectrum1559.graph
    sourceMap2465 fusedMap2465 sourceMap2465_checked fusedMap2465_checked
    DegreeOneSmallComparisons.comparison2465
#print axioms sourceMap2465_checked
#print axioms fusedMap2465_checked
#print axioms certified2465
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
