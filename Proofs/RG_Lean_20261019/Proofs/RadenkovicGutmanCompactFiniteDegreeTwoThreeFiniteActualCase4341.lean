/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4341 : Family 9 := level9.get ⟨455,by decide⟩
def sourceMap4341 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap4341 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4341_checked : acceptsGraphIso
    (source (graph core4341) (root 9) 2 2) DegreeTwoThreeSpectrum4833.graph sourceMap4341=true := by decide +kernel
theorem fusedMap4341_checked : acceptsGraphIso
    (fused (graph core4341) (root 9) 2 2) DegreeTwoThreeSpectrum4475.graph fusedMap4341=true := by decide +kernel
theorem certified4341 : Certified (graph core4341) (root 9) 2 2 :=
  of_native_maps core4341 DegreeTwoThreeSpectrum4833.graph DegreeTwoThreeSpectrum4475.graph
    sourceMap4341 fusedMap4341 sourceMap4341_checked fusedMap4341_checked
    DegreeTwoThreeFiniteComparisons.comparison4341
#print axioms sourceMap4341_checked
#print axioms fusedMap4341_checked
#print axioms certified4341
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
