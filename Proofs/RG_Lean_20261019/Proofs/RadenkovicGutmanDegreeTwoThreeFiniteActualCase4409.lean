/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4409 : Family 9 := level9.get ⟨617,by decide⟩
def sourceMap4409 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4409 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4409_checked : acceptsGraphIso
    (source (graph core4409) (root 9) 2 2) DegreeTwoThreeSpectrum4936.graph sourceMap4409=true := by decide +kernel
theorem fusedMap4409_checked : acceptsGraphIso
    (fused (graph core4409) (root 9) 2 2) DegreeTwoThreeSpectrum4331.graph fusedMap4409=true := by decide +kernel
theorem certified4409 : Certified (graph core4409) (root 9) 2 2 :=
  of_native_maps core4409 DegreeTwoThreeSpectrum4936.graph DegreeTwoThreeSpectrum4331.graph
    sourceMap4409 fusedMap4409 sourceMap4409_checked fusedMap4409_checked
    DegreeTwoThreeFiniteComparisons.comparison4409
#print axioms sourceMap4409_checked
#print axioms fusedMap4409_checked
#print axioms certified4409
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
