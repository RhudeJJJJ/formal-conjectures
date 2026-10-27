/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4119 : Family 8 := level8.get ⟨88,by decide⟩
def sourceMap4119 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,8,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap4119 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4119_checked : acceptsGraphIso
    (source (graph core4119) (root 8) 2 2) DegreeTwoThreeSpectrum3629.graph sourceMap4119=true := by decide +kernel
theorem fusedMap4119_checked : acceptsGraphIso
    (fused (graph core4119) (root 8) 2 2) DegreeTwoThreeSpectrum2415.graph fusedMap4119=true := by decide +kernel
theorem certified4119 : Certified (graph core4119) (root 8) 2 2 :=
  of_native_maps core4119 DegreeTwoThreeSpectrum3629.graph DegreeTwoThreeSpectrum2415.graph
    sourceMap4119 fusedMap4119 sourceMap4119_checked fusedMap4119_checked
    DegreeTwoThreeFiniteComparisons.comparison4119
#print axioms sourceMap4119_checked
#print axioms fusedMap4119_checked
#print axioms certified4119
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
