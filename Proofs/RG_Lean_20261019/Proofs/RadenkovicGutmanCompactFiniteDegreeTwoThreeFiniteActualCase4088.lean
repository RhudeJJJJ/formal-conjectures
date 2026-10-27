/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4088 : Family 7 := level7.get ⟨84,by decide⟩
def sourceMap4088 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,12,13,6,7,8,9,10,11] (sourceLabel 7 2 2 v)
def fusedMap4088 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4088_checked : acceptsGraphIso
    (source (graph core4088) (root 7) 2 2) DegreeTwoThreeSpectrum2293.graph sourceMap4088=true := by decide +kernel
theorem fusedMap4088_checked : acceptsGraphIso
    (fused (graph core4088) (root 7) 2 2) DegreeTwoThreeSpectrum1808.graph fusedMap4088=true := by decide +kernel
theorem certified4088 : Certified (graph core4088) (root 7) 2 2 :=
  of_native_maps core4088 DegreeTwoThreeSpectrum2293.graph DegreeTwoThreeSpectrum1808.graph
    sourceMap4088 fusedMap4088 sourceMap4088_checked fusedMap4088_checked
    DegreeTwoThreeFiniteComparisons.comparison4088
#print axioms sourceMap4088_checked
#print axioms fusedMap4088_checked
#print axioms certified4088
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
