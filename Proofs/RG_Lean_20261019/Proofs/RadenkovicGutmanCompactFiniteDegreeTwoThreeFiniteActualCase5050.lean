/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5050 : Family 10 := level10.get ⟨1802,by decide⟩
def sourceMap5050 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap5050 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,12,1,0,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5050_checked : acceptsGraphIso
    (source (graph core5050) (root 10) 2 2) DegreeTwoThreeSpectrum7651.graph sourceMap5050=true := by decide +kernel
theorem fusedMap5050_checked : acceptsGraphIso
    (fused (graph core5050) (root 10) 2 2) DegreeTwoThreeSpectrum7060.graph fusedMap5050=true := by decide +kernel
theorem certified5050 : Certified (graph core5050) (root 10) 2 2 :=
  of_native_maps core5050 DegreeTwoThreeSpectrum7651.graph DegreeTwoThreeSpectrum7060.graph
    sourceMap5050 fusedMap5050 sourceMap5050_checked fusedMap5050_checked
    DegreeTwoThreeFiniteComparisons.comparison5050
#print axioms sourceMap5050_checked
#print axioms fusedMap5050_checked
#print axioms certified5050
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
