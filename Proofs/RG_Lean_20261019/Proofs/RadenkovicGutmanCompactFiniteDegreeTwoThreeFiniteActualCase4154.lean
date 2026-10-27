/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4154 : Family 8 := level8.get ⟨176,by decide⟩
def sourceMap4154 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,7,8,9,1,2,3,4,5,6] (sourceLabel 8 2 2 v)
def fusedMap4154 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4154_checked : acceptsGraphIso
    (source (graph core4154) (root 8) 2 2) DegreeTwoThreeSpectrum3613.graph sourceMap4154=true := by decide +kernel
theorem fusedMap4154_checked : acceptsGraphIso
    (fused (graph core4154) (root 8) 2 2) DegreeTwoThreeSpectrum2916.graph fusedMap4154=true := by decide +kernel
theorem certified4154 : Certified (graph core4154) (root 8) 2 2 :=
  of_native_maps core4154 DegreeTwoThreeSpectrum3613.graph DegreeTwoThreeSpectrum2916.graph
    sourceMap4154 fusedMap4154 sourceMap4154_checked fusedMap4154_checked
    DegreeTwoThreeFiniteComparisons.comparison4154
#print axioms sourceMap4154_checked
#print axioms fusedMap4154_checked
#print axioms certified4154
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
