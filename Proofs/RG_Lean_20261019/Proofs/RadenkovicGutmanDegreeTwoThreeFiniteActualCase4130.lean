/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4130 : Family 8 := level8.get ⟨118,by decide⟩
def sourceMap4130 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,13,14,7,8,9,10,11,12] (sourceLabel 8 2 2 v)
def fusedMap4130 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4130_checked : acceptsGraphIso
    (source (graph core4130) (root 8) 2 2) DegreeTwoThreeSpectrum3267.graph sourceMap4130=true := by decide +kernel
theorem fusedMap4130_checked : acceptsGraphIso
    (fused (graph core4130) (root 8) 2 2) DegreeTwoThreeSpectrum2547.graph fusedMap4130=true := by decide +kernel
theorem certified4130 : Certified (graph core4130) (root 8) 2 2 :=
  of_native_maps core4130 DegreeTwoThreeSpectrum3267.graph DegreeTwoThreeSpectrum2547.graph
    sourceMap4130 fusedMap4130 sourceMap4130_checked fusedMap4130_checked
    DegreeTwoThreeFiniteComparisons.comparison4130
#print axioms sourceMap4130_checked
#print axioms fusedMap4130_checked
#print axioms certified4130
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
