/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4291 : Family 9 := level9.get ⟨328,by decide⟩
def sourceMap4291 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4291 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4291_checked : acceptsGraphIso
    (source (graph core4291) (root 9) 2 2) DegreeTwoThreeSpectrum4690.graph sourceMap4291=true := by decide +kernel
theorem fusedMap4291_checked : acceptsGraphIso
    (fused (graph core4291) (root 9) 2 2) DegreeTwoThreeSpectrum4201.graph fusedMap4291=true := by decide +kernel
theorem certified4291 : Certified (graph core4291) (root 9) 2 2 :=
  of_native_maps core4291 DegreeTwoThreeSpectrum4690.graph DegreeTwoThreeSpectrum4201.graph
    sourceMap4291 fusedMap4291 sourceMap4291_checked fusedMap4291_checked
    DegreeTwoThreeFiniteComparisons.comparison4291
#print axioms sourceMap4291_checked
#print axioms fusedMap4291_checked
#print axioms certified4291
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
