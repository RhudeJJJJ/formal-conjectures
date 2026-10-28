/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5191 : Family 8 := level8.get ⟨212,by decide⟩
def sourceMap5191 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,12,8,9,10,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5191 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5191_checked : acceptsGraphIso
    (source (graph core5191) (root 8) 2 4) DegreeTwoThreeSpectrum7197.graph sourceMap5191=true := by decide +kernel
theorem fusedMap5191_checked : acceptsGraphIso
    (fused (graph core5191) (root 8) 2 4) DegreeTwoThreeSpectrum5233.graph fusedMap5191=true := by decide +kernel
theorem certified5191 : Certified (graph core5191) (root 8) 2 4 :=
  of_native_maps core5191 DegreeTwoThreeSpectrum7197.graph DegreeTwoThreeSpectrum5233.graph
    sourceMap5191 fusedMap5191 sourceMap5191_checked fusedMap5191_checked
    DegreeTwoThreeFiniteComparisons.comparison5191
#print axioms sourceMap5191_checked
#print axioms fusedMap5191_checked
#print axioms certified5191
def sourceMap5191swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,12,0,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5191swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5191swap_checked : acceptsGraphIso
    (source (graph core5191) (root 8) 4 2) DegreeTwoThreeSpectrum7197.graph sourceMap5191swap=true := by decide +kernel
theorem fusedMap5191swap_checked : acceptsGraphIso
    (fused (graph core5191) (root 8) 4 2) DegreeTwoThreeSpectrum5233.graph fusedMap5191swap=true := by decide +kernel
theorem certified5191swap : Certified (graph core5191) (root 8) 4 2 :=
  of_native_maps core5191 DegreeTwoThreeSpectrum7197.graph DegreeTwoThreeSpectrum5233.graph
    sourceMap5191swap fusedMap5191swap sourceMap5191swap_checked fusedMap5191swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5191
#print axioms sourceMap5191swap_checked
#print axioms fusedMap5191swap_checked
#print axioms certified5191swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
