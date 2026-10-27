/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4294 : Family 9 := level9.get ⟨339,by decide⟩
def sourceMap4294 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4294 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4294_checked : acceptsGraphIso
    (source (graph core4294) (root 9) 2 2) DegreeTwoThreeSpectrum4705.graph sourceMap4294=true := by decide +kernel
theorem fusedMap4294_checked : acceptsGraphIso
    (fused (graph core4294) (root 9) 2 2) DegreeTwoThreeSpectrum4228.graph fusedMap4294=true := by decide +kernel
theorem certified4294 : Certified (graph core4294) (root 9) 2 2 :=
  of_native_maps core4294 DegreeTwoThreeSpectrum4705.graph DegreeTwoThreeSpectrum4228.graph
    sourceMap4294 fusedMap4294 sourceMap4294_checked fusedMap4294_checked
    DegreeTwoThreeFiniteComparisons.comparison4294
#print axioms sourceMap4294_checked
#print axioms fusedMap4294_checked
#print axioms certified4294
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
