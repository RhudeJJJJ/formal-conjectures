/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5045 : Family 10 := level10.get ⟨1751,by decide⟩
def sourceMap5045 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap5045 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5045_checked : acceptsGraphIso
    (source (graph core5045) (root 10) 2 2) DegreeTwoThreeSpectrum7646.graph sourceMap5045=true := by decide +kernel
theorem fusedMap5045_checked : acceptsGraphIso
    (fused (graph core5045) (root 10) 2 2) DegreeTwoThreeSpectrum6620.graph fusedMap5045=true := by decide +kernel
theorem certified5045 : Certified (graph core5045) (root 10) 2 2 :=
  of_native_maps core5045 DegreeTwoThreeSpectrum7646.graph DegreeTwoThreeSpectrum6620.graph
    sourceMap5045 fusedMap5045 sourceMap5045_checked fusedMap5045_checked
    DegreeTwoThreeFiniteComparisons.comparison5045
#print axioms sourceMap5045_checked
#print axioms fusedMap5045_checked
#print axioms certified5045
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
