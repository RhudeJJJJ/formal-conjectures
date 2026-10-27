/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4279 : Family 9 := level9.get ⟨298,by decide⟩
def sourceMap4279 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,10,11,12,13,14,15,8,9,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4279 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4279_checked : acceptsGraphIso
    (source (graph core4279) (root 9) 2 2) DegreeTwoThreeSpectrum4880.graph sourceMap4279=true := by decide +kernel
theorem fusedMap4279_checked : acceptsGraphIso
    (fused (graph core4279) (root 9) 2 2) DegreeTwoThreeSpectrum4128.graph fusedMap4279=true := by decide +kernel
theorem certified4279 : Certified (graph core4279) (root 9) 2 2 :=
  of_native_maps core4279 DegreeTwoThreeSpectrum4880.graph DegreeTwoThreeSpectrum4128.graph
    sourceMap4279 fusedMap4279 sourceMap4279_checked fusedMap4279_checked
    DegreeTwoThreeFiniteComparisons.comparison4279
#print axioms sourceMap4279_checked
#print axioms fusedMap4279_checked
#print axioms certified4279
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
