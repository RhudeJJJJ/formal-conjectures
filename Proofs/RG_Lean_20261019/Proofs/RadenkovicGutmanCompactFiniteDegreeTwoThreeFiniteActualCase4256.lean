/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4256 : Family 9 := level9.get ⟨236,by decide⟩
def sourceMap4256 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,15,14,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4256 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4256_checked : acceptsGraphIso
    (source (graph core4256) (root 9) 2 2) DegreeTwoThreeSpectrum4854.graph sourceMap4256=true := by decide +kernel
theorem fusedMap4256_checked : acceptsGraphIso
    (fused (graph core4256) (root 9) 2 2) DegreeTwoThreeSpectrum4029.graph fusedMap4256=true := by decide +kernel
theorem certified4256 : Certified (graph core4256) (root 9) 2 2 :=
  of_native_maps core4256 DegreeTwoThreeSpectrum4854.graph DegreeTwoThreeSpectrum4029.graph
    sourceMap4256 fusedMap4256 sourceMap4256_checked fusedMap4256_checked
    DegreeTwoThreeFiniteComparisons.comparison4256
#print axioms sourceMap4256_checked
#print axioms fusedMap4256_checked
#print axioms certified4256
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
