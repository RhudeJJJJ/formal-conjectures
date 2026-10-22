/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5361 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap5361 : (Vertices 5 ⊕ Fin 4 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,6,7,8,9,10,2,3,4,5,0,11,12,13,14,15] (sourceLabel 5 3 5 v)
def fusedMap5361 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15] (fusedLabel 5 3 5 v)
theorem sourceMap5361_checked : acceptsGraphIso
    (source (graph core5361) (root 5) 3 5) DegreeTwoThreeSpectrum4647.graph sourceMap5361=true := by decide +kernel
theorem fusedMap5361_checked : acceptsGraphIso
    (fused (graph core5361) (root 5) 3 5) DegreeTwoThreeSpectrum3902.graph fusedMap5361=true := by decide +kernel
theorem certified5361 : Certified (graph core5361) (root 5) 3 5 :=
  of_native_maps core5361 DegreeTwoThreeSpectrum4647.graph DegreeTwoThreeSpectrum3902.graph
    sourceMap5361 fusedMap5361 sourceMap5361_checked fusedMap5361_checked
    DegreeTwoThreeFiniteComparisons.comparison5361
#print axioms sourceMap5361_checked
#print axioms fusedMap5361_checked
#print axioms certified5361
def sourceMap5361swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 4) → Fin 16 :=
  fun v => ![1,6,7,8,9,10,0,11,12,13,14,15,2,3,4,5] (sourceLabel 5 5 3 v)
def fusedMap5361swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15] (fusedLabel 5 5 3 v)
theorem sourceMap5361swap_checked : acceptsGraphIso
    (source (graph core5361) (root 5) 5 3) DegreeTwoThreeSpectrum4647.graph sourceMap5361swap=true := by decide +kernel
theorem fusedMap5361swap_checked : acceptsGraphIso
    (fused (graph core5361) (root 5) 5 3) DegreeTwoThreeSpectrum3902.graph fusedMap5361swap=true := by decide +kernel
theorem certified5361swap : Certified (graph core5361) (root 5) 5 3 :=
  of_native_maps core5361 DegreeTwoThreeSpectrum4647.graph DegreeTwoThreeSpectrum3902.graph
    sourceMap5361swap fusedMap5361swap sourceMap5361swap_checked fusedMap5361swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5361
#print axioms sourceMap5361swap_checked
#print axioms fusedMap5361swap_checked
#print axioms certified5361swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
