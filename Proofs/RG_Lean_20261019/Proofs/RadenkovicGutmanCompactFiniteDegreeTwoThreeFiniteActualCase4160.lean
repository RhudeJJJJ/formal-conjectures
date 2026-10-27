/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4160 : Family 8 := level8.get ⟨193,by decide⟩
def sourceMap4160 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4160 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4160_checked : acceptsGraphIso
    (source (graph core4160) (root 8) 2 2) DegreeTwoThreeSpectrum3754.graph sourceMap4160=true := by decide +kernel
theorem fusedMap4160_checked : acceptsGraphIso
    (fused (graph core4160) (root 8) 2 2) DegreeTwoThreeSpectrum2442.graph fusedMap4160=true := by decide +kernel
theorem certified4160 : Certified (graph core4160) (root 8) 2 2 :=
  of_native_maps core4160 DegreeTwoThreeSpectrum3754.graph DegreeTwoThreeSpectrum2442.graph
    sourceMap4160 fusedMap4160 sourceMap4160_checked fusedMap4160_checked
    DegreeTwoThreeFiniteComparisons.comparison4160
#print axioms sourceMap4160_checked
#print axioms fusedMap4160_checked
#print axioms certified4160
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
