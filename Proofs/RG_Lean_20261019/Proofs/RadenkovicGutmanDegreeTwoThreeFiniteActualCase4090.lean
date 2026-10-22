/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4090 : Family 7 := level7.get ⟨88,by decide⟩
def sourceMap4090 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,12,13,6,7,8,9,10,11] (sourceLabel 7 2 2 v)
def fusedMap4090 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4090_checked : acceptsGraphIso
    (source (graph core4090) (root 7) 2 2) DegreeTwoThreeSpectrum2300.graph sourceMap4090=true := by decide +kernel
theorem fusedMap4090_checked : acceptsGraphIso
    (fused (graph core4090) (root 7) 2 2) DegreeTwoThreeSpectrum1820.graph fusedMap4090=true := by decide +kernel
theorem certified4090 : Certified (graph core4090) (root 7) 2 2 :=
  of_native_maps core4090 DegreeTwoThreeSpectrum2300.graph DegreeTwoThreeSpectrum1820.graph
    sourceMap4090 fusedMap4090 sourceMap4090_checked fusedMap4090_checked
    DegreeTwoThreeFiniteComparisons.comparison4090
#print axioms sourceMap4090_checked
#print axioms fusedMap4090_checked
#print axioms certified4090
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
