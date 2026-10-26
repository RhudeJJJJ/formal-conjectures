/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3920 : Family 8 := level8.get ⟨266,by decide⟩
def sourceMap3920 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3920 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3920_checked : acceptsGraphIso
    (source (graph core3920) (root 8) 1 4) DegreeTwoThreeSpectrum4672.graph sourceMap3920=true := by decide +kernel
theorem fusedMap3920_checked : acceptsGraphIso
    (fused (graph core3920) (root 8) 1 4) DegreeTwoThreeSpectrum4173.graph fusedMap3920=true := by decide +kernel
theorem certified3920 : Certified (graph core3920) (root 8) 1 4 :=
  of_native_maps core3920 DegreeTwoThreeSpectrum4672.graph DegreeTwoThreeSpectrum4173.graph
    sourceMap3920 fusedMap3920 sourceMap3920_checked fusedMap3920_checked
    DegreeTwoThreeFiniteComparisons.comparison3920
#print axioms sourceMap3920_checked
#print axioms fusedMap3920_checked
#print axioms certified3920
def sourceMap3920swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3920swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3920swap_checked : acceptsGraphIso
    (source (graph core3920) (root 8) 4 1) DegreeTwoThreeSpectrum4672.graph sourceMap3920swap=true := by decide +kernel
theorem fusedMap3920swap_checked : acceptsGraphIso
    (fused (graph core3920) (root 8) 4 1) DegreeTwoThreeSpectrum4173.graph fusedMap3920swap=true := by decide +kernel
theorem certified3920swap : Certified (graph core3920) (root 8) 4 1 :=
  of_native_maps core3920 DegreeTwoThreeSpectrum4672.graph DegreeTwoThreeSpectrum4173.graph
    sourceMap3920swap fusedMap3920swap sourceMap3920swap_checked fusedMap3920swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3920
#print axioms sourceMap3920swap_checked
#print axioms fusedMap3920swap_checked
#print axioms certified3920swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
