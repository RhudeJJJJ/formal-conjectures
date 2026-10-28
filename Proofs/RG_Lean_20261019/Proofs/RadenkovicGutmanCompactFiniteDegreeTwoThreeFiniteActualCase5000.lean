/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5000 : Family 10 := level10.get ⟨1621,by decide⟩
def sourceMap5000 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap5000 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5000_checked : acceptsGraphIso
    (source (graph core5000) (root 10) 2 2) DegreeTwoThreeSpectrum7601.graph sourceMap5000=true := by decide +kernel
theorem fusedMap5000_checked : acceptsGraphIso
    (fused (graph core5000) (root 10) 2 2) DegreeTwoThreeSpectrum6179.graph fusedMap5000=true := by decide +kernel
theorem certified5000 : Certified (graph core5000) (root 10) 2 2 :=
  of_native_maps core5000 DegreeTwoThreeSpectrum7601.graph DegreeTwoThreeSpectrum6179.graph
    sourceMap5000 fusedMap5000 sourceMap5000_checked fusedMap5000_checked
    DegreeTwoThreeFiniteComparisons.comparison5000
#print axioms sourceMap5000_checked
#print axioms fusedMap5000_checked
#print axioms certified5000
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
