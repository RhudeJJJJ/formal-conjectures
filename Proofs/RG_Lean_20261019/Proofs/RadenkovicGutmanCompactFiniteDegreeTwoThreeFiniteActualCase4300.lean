/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4300 : Family 9 := level9.get ⟨351,by decide⟩
def sourceMap4300 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap4300 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4300_checked : acceptsGraphIso
    (source (graph core4300) (root 9) 2 2) DegreeTwoThreeSpectrum4719.graph sourceMap4300=true := by decide +kernel
theorem fusedMap4300_checked : acceptsGraphIso
    (fused (graph core4300) (root 9) 2 2) DegreeTwoThreeSpectrum4253.graph fusedMap4300=true := by decide +kernel
theorem certified4300 : Certified (graph core4300) (root 9) 2 2 :=
  of_native_maps core4300 DegreeTwoThreeSpectrum4719.graph DegreeTwoThreeSpectrum4253.graph
    sourceMap4300 fusedMap4300 sourceMap4300_checked fusedMap4300_checked
    DegreeTwoThreeFiniteComparisons.comparison4300
#print axioms sourceMap4300_checked
#print axioms fusedMap4300_checked
#print axioms certified4300
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
