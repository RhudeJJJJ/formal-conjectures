/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4264 : Family 9 := level9.get ⟨257,by decide⟩
def sourceMap4264 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4264 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4264_checked : acceptsGraphIso
    (source (graph core4264) (root 9) 2 2) DegreeTwoThreeSpectrum4886.graph sourceMap4264=true := by decide +kernel
theorem fusedMap4264_checked : acceptsGraphIso
    (fused (graph core4264) (root 9) 2 2) DegreeTwoThreeSpectrum4066.graph fusedMap4264=true := by decide +kernel
theorem certified4264 : Certified (graph core4264) (root 9) 2 2 :=
  of_native_maps core4264 DegreeTwoThreeSpectrum4886.graph DegreeTwoThreeSpectrum4066.graph
    sourceMap4264 fusedMap4264 sourceMap4264_checked fusedMap4264_checked
    DegreeTwoThreeFiniteComparisons.comparison4264
#print axioms sourceMap4264_checked
#print axioms fusedMap4264_checked
#print axioms certified4264
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
