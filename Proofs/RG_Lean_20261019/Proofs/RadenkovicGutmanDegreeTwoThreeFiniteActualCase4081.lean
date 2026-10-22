/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4081 : Family 7 := level7.get ⟨68,by decide⟩
def sourceMap4081 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,12,13,6,7,8,9,10,11] (sourceLabel 7 2 2 v)
def fusedMap4081 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4081_checked : acceptsGraphIso
    (source (graph core4081) (root 7) 2 2) DegreeTwoThreeSpectrum2264.graph sourceMap4081=true := by decide +kernel
theorem fusedMap4081_checked : acceptsGraphIso
    (fused (graph core4081) (root 7) 2 2) DegreeTwoThreeSpectrum1747.graph fusedMap4081=true := by decide +kernel
theorem certified4081 : Certified (graph core4081) (root 7) 2 2 :=
  of_native_maps core4081 DegreeTwoThreeSpectrum2264.graph DegreeTwoThreeSpectrum1747.graph
    sourceMap4081 fusedMap4081 sourceMap4081_checked fusedMap4081_checked
    DegreeTwoThreeFiniteComparisons.comparison4081
#print axioms sourceMap4081_checked
#print axioms fusedMap4081_checked
#print axioms certified4081
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
