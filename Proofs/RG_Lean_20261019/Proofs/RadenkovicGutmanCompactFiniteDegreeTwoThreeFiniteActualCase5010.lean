/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5010 : Family 10 := level10.get ⟨1641,by decide⟩
def sourceMap5010 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap5010 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5010_checked : acceptsGraphIso
    (source (graph core5010) (root 10) 2 2) DegreeTwoThreeSpectrum7611.graph sourceMap5010=true := by decide +kernel
theorem fusedMap5010_checked : acceptsGraphIso
    (fused (graph core5010) (root 10) 2 2) DegreeTwoThreeSpectrum6217.graph fusedMap5010=true := by decide +kernel
theorem certified5010 : Certified (graph core5010) (root 10) 2 2 :=
  of_native_maps core5010 DegreeTwoThreeSpectrum7611.graph DegreeTwoThreeSpectrum6217.graph
    sourceMap5010 fusedMap5010 sourceMap5010_checked fusedMap5010_checked
    DegreeTwoThreeFiniteComparisons.comparison5010
#print axioms sourceMap5010_checked
#print axioms fusedMap5010_checked
#print axioms certified5010
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
