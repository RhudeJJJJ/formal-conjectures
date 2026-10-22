/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5384 : Family 6 := level6.get ⟨13,by decide⟩
def sourceMap5384 : (Vertices 6 ⊕ Fin 5 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 4 4 v)
def fusedMap5384 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 4 4 v)
theorem sourceMap5384_checked : acceptsGraphIso
    (source (graph core5384) (root 6) 4 4) DegreeTwoThreeSpectrum7043.graph sourceMap5384=true := by decide +kernel
theorem fusedMap5384_checked : acceptsGraphIso
    (fused (graph core5384) (root 6) 4 4) DegreeTwoThreeSpectrum5033.graph fusedMap5384=true := by decide +kernel
theorem certified5384 : Certified (graph core5384) (root 6) 4 4 :=
  of_native_maps core5384 DegreeTwoThreeSpectrum7043.graph DegreeTwoThreeSpectrum5033.graph
    sourceMap5384 fusedMap5384 sourceMap5384_checked fusedMap5384_checked
    DegreeTwoThreeFiniteComparisons.comparison5384
#print axioms sourceMap5384_checked
#print axioms fusedMap5384_checked
#print axioms certified5384
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
