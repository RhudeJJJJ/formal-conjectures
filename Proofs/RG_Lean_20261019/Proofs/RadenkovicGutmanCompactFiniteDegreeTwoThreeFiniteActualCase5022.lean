/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5022 : Family 10 := level10.get ⟨1678,by decide⟩
def sourceMap5022 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap5022 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5022_checked : acceptsGraphIso
    (source (graph core5022) (root 10) 2 2) DegreeTwoThreeSpectrum7623.graph sourceMap5022=true := by decide +kernel
theorem fusedMap5022_checked : acceptsGraphIso
    (fused (graph core5022) (root 10) 2 2) DegreeTwoThreeSpectrum6338.graph fusedMap5022=true := by decide +kernel
theorem certified5022 : Certified (graph core5022) (root 10) 2 2 :=
  of_native_maps core5022 DegreeTwoThreeSpectrum7623.graph DegreeTwoThreeSpectrum6338.graph
    sourceMap5022 fusedMap5022 sourceMap5022_checked fusedMap5022_checked
    DegreeTwoThreeFiniteComparisons.comparison5022
#print axioms sourceMap5022_checked
#print axioms fusedMap5022_checked
#print axioms certified5022
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
