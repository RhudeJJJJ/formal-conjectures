/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4095 : Family 7 := level7.get ⟨102,by decide⟩
def sourceMap4095 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,7,8,9,10,11,12,13,1,2,3,4,5,6] (sourceLabel 7 2 2 v)
def fusedMap4095 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4095_checked : acceptsGraphIso
    (source (graph core4095) (root 7) 2 2) DegreeTwoThreeSpectrum2307.graph sourceMap4095=true := by decide +kernel
theorem fusedMap4095_checked : acceptsGraphIso
    (fused (graph core4095) (root 7) 2 2) DegreeTwoThreeSpectrum1934.graph fusedMap4095=true := by decide +kernel
theorem certified4095 : Certified (graph core4095) (root 7) 2 2 :=
  of_native_maps core4095 DegreeTwoThreeSpectrum2307.graph DegreeTwoThreeSpectrum1934.graph
    sourceMap4095 fusedMap4095 sourceMap4095_checked fusedMap4095_checked
    DegreeTwoThreeFiniteComparisons.comparison4095
#print axioms sourceMap4095_checked
#print axioms fusedMap4095_checked
#print axioms certified4095
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
