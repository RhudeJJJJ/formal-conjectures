/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5052 : Family 10 := level10.get ⟨1807,by decide⟩
def sourceMap5052 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap5052 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,12,1,0,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5052_checked : acceptsGraphIso
    (source (graph core5052) (root 10) 2 2) DegreeTwoThreeSpectrum7653.graph sourceMap5052=true := by decide +kernel
theorem fusedMap5052_checked : acceptsGraphIso
    (fused (graph core5052) (root 10) 2 2) DegreeTwoThreeSpectrum7070.graph fusedMap5052=true := by decide +kernel
theorem certified5052 : Certified (graph core5052) (root 10) 2 2 :=
  of_native_maps core5052 DegreeTwoThreeSpectrum7653.graph DegreeTwoThreeSpectrum7070.graph
    sourceMap5052 fusedMap5052 sourceMap5052_checked fusedMap5052_checked
    DegreeTwoThreeFiniteComparisons.comparison5052
#print axioms sourceMap5052_checked
#print axioms fusedMap5052_checked
#print axioms certified5052
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
