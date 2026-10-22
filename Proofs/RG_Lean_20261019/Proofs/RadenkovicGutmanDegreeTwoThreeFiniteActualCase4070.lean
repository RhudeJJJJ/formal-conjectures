/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4070 : Family 7 := level7.get ⟨41,by decide⟩
def sourceMap4070 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,13,7,8,9,10,11,12] (sourceLabel 7 2 2 v)
def fusedMap4070 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4070_checked : acceptsGraphIso
    (source (graph core4070) (root 7) 2 2) DegreeTwoThreeSpectrum2106.graph sourceMap4070=true := by decide +kernel
theorem fusedMap4070_checked : acceptsGraphIso
    (fused (graph core4070) (root 7) 2 2) DegreeTwoThreeSpectrum1814.graph fusedMap4070=true := by decide +kernel
theorem certified4070 : Certified (graph core4070) (root 7) 2 2 :=
  of_native_maps core4070 DegreeTwoThreeSpectrum2106.graph DegreeTwoThreeSpectrum1814.graph
    sourceMap4070 fusedMap4070 sourceMap4070_checked fusedMap4070_checked
    DegreeTwoThreeFiniteComparisons.comparison4070
#print axioms sourceMap4070_checked
#print axioms fusedMap4070_checked
#print axioms certified4070
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
