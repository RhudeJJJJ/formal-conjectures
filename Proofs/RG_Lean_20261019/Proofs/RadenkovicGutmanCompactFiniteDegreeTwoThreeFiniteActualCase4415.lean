/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4415 : Family 9 := level9.get ⟨636,by decide⟩
def sourceMap4415 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4415 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4415_checked : acceptsGraphIso
    (source (graph core4415) (root 9) 2 2) DegreeTwoThreeSpectrum4942.graph sourceMap4415=true := by decide +kernel
theorem fusedMap4415_checked : acceptsGraphIso
    (fused (graph core4415) (root 9) 2 2) DegreeTwoThreeSpectrum4398.graph fusedMap4415=true := by decide +kernel
theorem certified4415 : Certified (graph core4415) (root 9) 2 2 :=
  of_native_maps core4415 DegreeTwoThreeSpectrum4942.graph DegreeTwoThreeSpectrum4398.graph
    sourceMap4415 fusedMap4415 sourceMap4415_checked fusedMap4415_checked
    DegreeTwoThreeFiniteComparisons.comparison4415
#print axioms sourceMap4415_checked
#print axioms fusedMap4415_checked
#print axioms certified4415
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
