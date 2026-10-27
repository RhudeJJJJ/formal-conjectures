/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4394 : Family 9 := level9.get ⟨580,by decide⟩
def sourceMap4394 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,12,13,14,15,6,7,8,9,10,11] (sourceLabel 9 2 2 v)
def fusedMap4394 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4394_checked : acceptsGraphIso
    (source (graph core4394) (root 9) 2 2) DegreeTwoThreeSpectrum4921.graph sourceMap4394=true := by decide +kernel
theorem fusedMap4394_checked : acceptsGraphIso
    (fused (graph core4394) (root 9) 2 2) DegreeTwoThreeSpectrum4237.graph fusedMap4394=true := by decide +kernel
theorem certified4394 : Certified (graph core4394) (root 9) 2 2 :=
  of_native_maps core4394 DegreeTwoThreeSpectrum4921.graph DegreeTwoThreeSpectrum4237.graph
    sourceMap4394 fusedMap4394 sourceMap4394_checked fusedMap4394_checked
    DegreeTwoThreeFiniteComparisons.comparison4394
#print axioms sourceMap4394_checked
#print axioms fusedMap4394_checked
#print axioms certified4394
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
