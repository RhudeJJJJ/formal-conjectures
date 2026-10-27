/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4348 : Family 9 := level9.get ⟨473,by decide⟩
def sourceMap4348 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4348 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4348_checked : acceptsGraphIso
    (source (graph core4348) (root 9) 2 2) DegreeTwoThreeSpectrum4851.graph sourceMap4348=true := by decide +kernel
theorem fusedMap4348_checked : acceptsGraphIso
    (fused (graph core4348) (root 9) 2 2) DegreeTwoThreeSpectrum4508.graph fusedMap4348=true := by decide +kernel
theorem certified4348 : Certified (graph core4348) (root 9) 2 2 :=
  of_native_maps core4348 DegreeTwoThreeSpectrum4851.graph DegreeTwoThreeSpectrum4508.graph
    sourceMap4348 fusedMap4348 sourceMap4348_checked fusedMap4348_checked
    DegreeTwoThreeFiniteComparisons.comparison4348
#print axioms sourceMap4348_checked
#print axioms fusedMap4348_checked
#print axioms certified4348
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
