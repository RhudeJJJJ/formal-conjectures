/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4091 : Family 7 := level7.get ⟨90,by decide⟩
def sourceMap4091 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap4091 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4091_checked : acceptsGraphIso
    (source (graph core4091) (root 7) 2 2) DegreeTwoThreeSpectrum2302.graph sourceMap4091=true := by decide +kernel
theorem fusedMap4091_checked : acceptsGraphIso
    (fused (graph core4091) (root 7) 2 2) DegreeTwoThreeSpectrum1830.graph fusedMap4091=true := by decide +kernel
theorem certified4091 : Certified (graph core4091) (root 7) 2 2 :=
  of_native_maps core4091 DegreeTwoThreeSpectrum2302.graph DegreeTwoThreeSpectrum1830.graph
    sourceMap4091 fusedMap4091 sourceMap4091_checked fusedMap4091_checked
    DegreeTwoThreeFiniteComparisons.comparison4091
#print axioms sourceMap4091_checked
#print axioms fusedMap4091_checked
#print axioms certified4091
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
