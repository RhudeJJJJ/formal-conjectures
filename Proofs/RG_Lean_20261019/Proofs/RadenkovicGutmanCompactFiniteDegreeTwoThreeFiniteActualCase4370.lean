/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4370 : Family 9 := level9.get ⟨519,by decide⟩
def sourceMap4370 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,11,12,13,14,15,1,2,3,4,5,6,7,8,9,10] (sourceLabel 9 2 2 v)
def fusedMap4370 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4370_checked : acceptsGraphIso
    (source (graph core4370) (root 9) 2 2) DegreeTwoThreeSpectrum4838.graph sourceMap4370=true := by decide +kernel
theorem fusedMap4370_checked : acceptsGraphIso
    (fused (graph core4370) (root 9) 2 2) DegreeTwoThreeSpectrum4612.graph fusedMap4370=true := by decide +kernel
theorem certified4370 : Certified (graph core4370) (root 9) 2 2 :=
  of_native_maps core4370 DegreeTwoThreeSpectrum4838.graph DegreeTwoThreeSpectrum4612.graph
    sourceMap4370 fusedMap4370 sourceMap4370_checked fusedMap4370_checked
    DegreeTwoThreeFiniteComparisons.comparison4370
#print axioms sourceMap4370_checked
#print axioms fusedMap4370_checked
#print axioms certified4370
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
