/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4253 : Family 9 := level9.get ⟨224,by decide⟩
def sourceMap4253 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4253 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4253_checked : acceptsGraphIso
    (source (graph core4253) (root 9) 2 2) DegreeTwoThreeSpectrum4834.graph sourceMap4253=true := by decide +kernel
theorem fusedMap4253_checked : acceptsGraphIso
    (fused (graph core4253) (root 9) 2 2) DegreeTwoThreeSpectrum4013.graph fusedMap4253=true := by decide +kernel
theorem certified4253 : Certified (graph core4253) (root 9) 2 2 :=
  of_native_maps core4253 DegreeTwoThreeSpectrum4834.graph DegreeTwoThreeSpectrum4013.graph
    sourceMap4253 fusedMap4253 sourceMap4253_checked fusedMap4253_checked
    DegreeTwoThreeFiniteComparisons.comparison4253
#print axioms sourceMap4253_checked
#print axioms fusedMap4253_checked
#print axioms certified4253
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
