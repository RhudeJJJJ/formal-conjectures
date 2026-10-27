/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4262 : Family 9 := level9.get ⟨248,by decide⟩
def sourceMap4262 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap4262 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4262_checked : acceptsGraphIso
    (source (graph core4262) (root 9) 2 2) DegreeTwoThreeSpectrum4857.graph sourceMap4262=true := by decide +kernel
theorem fusedMap4262_checked : acceptsGraphIso
    (fused (graph core4262) (root 9) 2 2) DegreeTwoThreeSpectrum4049.graph fusedMap4262=true := by decide +kernel
theorem certified4262 : Certified (graph core4262) (root 9) 2 2 :=
  of_native_maps core4262 DegreeTwoThreeSpectrum4857.graph DegreeTwoThreeSpectrum4049.graph
    sourceMap4262 fusedMap4262 sourceMap4262_checked fusedMap4262_checked
    DegreeTwoThreeFiniteComparisons.comparison4262
#print axioms sourceMap4262_checked
#print axioms fusedMap4262_checked
#print axioms certified4262
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
