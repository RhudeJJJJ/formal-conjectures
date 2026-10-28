/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5034 : Family 10 := level10.get ⟨1717,by decide⟩
def sourceMap5034 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap5034 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5034_checked : acceptsGraphIso
    (source (graph core5034) (root 10) 2 2) DegreeTwoThreeSpectrum7635.graph sourceMap5034=true := by decide +kernel
theorem fusedMap5034_checked : acceptsGraphIso
    (fused (graph core5034) (root 10) 2 2) DegreeTwoThreeSpectrum6503.graph fusedMap5034=true := by decide +kernel
theorem certified5034 : Certified (graph core5034) (root 10) 2 2 :=
  of_native_maps core5034 DegreeTwoThreeSpectrum7635.graph DegreeTwoThreeSpectrum6503.graph
    sourceMap5034 fusedMap5034 sourceMap5034_checked fusedMap5034_checked
    DegreeTwoThreeFiniteComparisons.comparison5034
#print axioms sourceMap5034_checked
#print axioms fusedMap5034_checked
#print axioms certified5034
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
