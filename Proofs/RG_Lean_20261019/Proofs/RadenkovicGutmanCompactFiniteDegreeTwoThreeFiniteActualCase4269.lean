/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4269 : Family 9 := level9.get ⟨272,by decide⟩
def sourceMap4269 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4269 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4269_checked : acceptsGraphIso
    (source (graph core4269) (root 9) 2 2) DegreeTwoThreeSpectrum4893.graph sourceMap4269=true := by decide +kernel
theorem fusedMap4269_checked : acceptsGraphIso
    (fused (graph core4269) (root 9) 2 2) DegreeTwoThreeSpectrum4085.graph fusedMap4269=true := by decide +kernel
theorem certified4269 : Certified (graph core4269) (root 9) 2 2 :=
  of_native_maps core4269 DegreeTwoThreeSpectrum4893.graph DegreeTwoThreeSpectrum4085.graph
    sourceMap4269 fusedMap4269 sourceMap4269_checked fusedMap4269_checked
    DegreeTwoThreeFiniteComparisons.comparison4269
#print axioms sourceMap4269_checked
#print axioms fusedMap4269_checked
#print axioms certified4269
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
