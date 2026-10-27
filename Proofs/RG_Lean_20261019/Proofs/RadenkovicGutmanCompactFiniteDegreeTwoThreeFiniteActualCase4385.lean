/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4385 : Family 9 := level9.get ⟨563,by decide⟩
def sourceMap4385 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4385 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4385_checked : acceptsGraphIso
    (source (graph core4385) (root 9) 2 2) DegreeTwoThreeSpectrum4912.graph sourceMap4385=true := by decide +kernel
theorem fusedMap4385_checked : acceptsGraphIso
    (fused (graph core4385) (root 9) 2 2) DegreeTwoThreeSpectrum4206.graph fusedMap4385=true := by decide +kernel
theorem certified4385 : Certified (graph core4385) (root 9) 2 2 :=
  of_native_maps core4385 DegreeTwoThreeSpectrum4912.graph DegreeTwoThreeSpectrum4206.graph
    sourceMap4385 fusedMap4385 sourceMap4385_checked fusedMap4385_checked
    DegreeTwoThreeFiniteComparisons.comparison4385
#print axioms sourceMap4385_checked
#print axioms fusedMap4385_checked
#print axioms certified4385
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
