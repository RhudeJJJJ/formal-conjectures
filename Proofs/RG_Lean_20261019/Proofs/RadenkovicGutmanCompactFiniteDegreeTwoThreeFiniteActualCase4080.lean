/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4080 : Family 7 := level7.get ⟨67,by decide⟩
def sourceMap4080 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,13,7,8,9,10,11,12] (sourceLabel 7 2 2 v)
def fusedMap4080 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4080_checked : acceptsGraphIso
    (source (graph core4080) (root 7) 2 2) DegreeTwoThreeSpectrum2260.graph sourceMap4080=true := by decide +kernel
theorem fusedMap4080_checked : acceptsGraphIso
    (fused (graph core4080) (root 7) 2 2) DegreeTwoThreeSpectrum1744.graph fusedMap4080=true := by decide +kernel
theorem certified4080 : Certified (graph core4080) (root 7) 2 2 :=
  of_native_maps core4080 DegreeTwoThreeSpectrum2260.graph DegreeTwoThreeSpectrum1744.graph
    sourceMap4080 fusedMap4080 sourceMap4080_checked fusedMap4080_checked
    DegreeTwoThreeFiniteComparisons.comparison4080
#print axioms sourceMap4080_checked
#print axioms fusedMap4080_checked
#print axioms certified4080
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
