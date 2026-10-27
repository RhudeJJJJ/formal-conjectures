/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4414 : Family 9 := level9.get ⟨635,by decide⟩
def sourceMap4414 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4414 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4414_checked : acceptsGraphIso
    (source (graph core4414) (root 9) 2 2) DegreeTwoThreeSpectrum4941.graph sourceMap4414=true := by decide +kernel
theorem fusedMap4414_checked : acceptsGraphIso
    (fused (graph core4414) (root 9) 2 2) DegreeTwoThreeSpectrum4397.graph fusedMap4414=true := by decide +kernel
theorem certified4414 : Certified (graph core4414) (root 9) 2 2 :=
  of_native_maps core4414 DegreeTwoThreeSpectrum4941.graph DegreeTwoThreeSpectrum4397.graph
    sourceMap4414 fusedMap4414 sourceMap4414_checked fusedMap4414_checked
    DegreeTwoThreeFiniteComparisons.comparison4414
#print axioms sourceMap4414_checked
#print axioms fusedMap4414_checked
#print axioms certified4414
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
