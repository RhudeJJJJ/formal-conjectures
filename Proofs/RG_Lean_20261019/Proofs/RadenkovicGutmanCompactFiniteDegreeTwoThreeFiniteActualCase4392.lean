/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4392 : Family 9 := level9.get ⟨577,by decide⟩
def sourceMap4392 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4392 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4392_checked : acceptsGraphIso
    (source (graph core4392) (root 9) 2 2) DegreeTwoThreeSpectrum4919.graph sourceMap4392=true := by decide +kernel
theorem fusedMap4392_checked : acceptsGraphIso
    (fused (graph core4392) (root 9) 2 2) DegreeTwoThreeSpectrum4233.graph fusedMap4392=true := by decide +kernel
theorem certified4392 : Certified (graph core4392) (root 9) 2 2 :=
  of_native_maps core4392 DegreeTwoThreeSpectrum4919.graph DegreeTwoThreeSpectrum4233.graph
    sourceMap4392 fusedMap4392 sourceMap4392_checked fusedMap4392_checked
    DegreeTwoThreeFiniteComparisons.comparison4392
#print axioms sourceMap4392_checked
#print axioms fusedMap4392_checked
#print axioms certified4392
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
