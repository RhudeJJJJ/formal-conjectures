/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4287 : Family 9 := level9.get ⟨312,by decide⟩
def sourceMap4287 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,12,13,14,15,8,9,10,11,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4287 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4287_checked : acceptsGraphIso
    (source (graph core4287) (root 9) 2 2) DegreeTwoThreeSpectrum4868.graph sourceMap4287=true := by decide +kernel
theorem fusedMap4287_checked : acceptsGraphIso
    (fused (graph core4287) (root 9) 2 2) DegreeTwoThreeSpectrum4155.graph fusedMap4287=true := by decide +kernel
theorem certified4287 : Certified (graph core4287) (root 9) 2 2 :=
  of_native_maps core4287 DegreeTwoThreeSpectrum4868.graph DegreeTwoThreeSpectrum4155.graph
    sourceMap4287 fusedMap4287 sourceMap4287_checked fusedMap4287_checked
    DegreeTwoThreeFiniteComparisons.comparison4287
#print axioms sourceMap4287_checked
#print axioms fusedMap4287_checked
#print axioms certified4287
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
