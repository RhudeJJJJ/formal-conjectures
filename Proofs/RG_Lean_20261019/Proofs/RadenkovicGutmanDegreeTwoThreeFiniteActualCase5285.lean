/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5285 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap5285 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,10,7,8,9,1,0,11,12,13,14,15] (sourceLabel 5 2 6 v)
def fusedMap5285 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 2 6 v)
theorem sourceMap5285_checked : acceptsGraphIso
    (source (graph core5285) (root 5) 2 6) DegreeTwoThreeSpectrum4336.graph sourceMap5285=true := by decide +kernel
theorem fusedMap5285_checked : acceptsGraphIso
    (fused (graph core5285) (root 5) 2 6) DegreeTwoThreeSpectrum3856.graph fusedMap5285=true := by decide +kernel
theorem certified5285 : Certified (graph core5285) (root 5) 2 6 :=
  of_native_maps core5285 DegreeTwoThreeSpectrum4336.graph DegreeTwoThreeSpectrum3856.graph
    sourceMap5285 fusedMap5285 sourceMap5285_checked fusedMap5285_checked
    DegreeTwoThreeFiniteComparisons.comparison5285
#print axioms sourceMap5285_checked
#print axioms fusedMap5285_checked
#print axioms certified5285
def sourceMap5285swap : (Vertices 5 ⊕ Fin 7 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,3,4,5,6,10,1,0,11,12,13,14,15,7,8,9] (sourceLabel 5 6 2 v)
def fusedMap5285swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 6 2 v)
theorem sourceMap5285swap_checked : acceptsGraphIso
    (source (graph core5285) (root 5) 6 2) DegreeTwoThreeSpectrum4336.graph sourceMap5285swap=true := by decide +kernel
theorem fusedMap5285swap_checked : acceptsGraphIso
    (fused (graph core5285) (root 5) 6 2) DegreeTwoThreeSpectrum3856.graph fusedMap5285swap=true := by decide +kernel
theorem certified5285swap : Certified (graph core5285) (root 5) 6 2 :=
  of_native_maps core5285 DegreeTwoThreeSpectrum4336.graph DegreeTwoThreeSpectrum3856.graph
    sourceMap5285swap fusedMap5285swap sourceMap5285swap_checked fusedMap5285swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5285
#print axioms sourceMap5285swap_checked
#print axioms fusedMap5285swap_checked
#print axioms certified5285swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
