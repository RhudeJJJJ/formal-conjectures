/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3625 : Family 8 := level8.get ⟨242,by decide⟩
def sourceMap3625 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3625 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3625_checked : acceptsGraphIso
    (source (graph core3625) (root 8) 0 6) DegreeTwoThreeSpectrum6603.graph sourceMap3625=true := by decide +kernel
theorem fusedMap3625_checked : acceptsGraphIso
    (fused (graph core3625) (root 8) 0 6) DegreeTwoThreeSpectrum5485.graph fusedMap3625=true := by decide +kernel
theorem certified3625 : Certified (graph core3625) (root 8) 0 6 :=
  of_native_maps core3625 DegreeTwoThreeSpectrum6603.graph DegreeTwoThreeSpectrum5485.graph
    sourceMap3625 fusedMap3625 sourceMap3625_checked fusedMap3625_checked
    DegreeTwoThreeFiniteComparisons.comparison3625
#print axioms sourceMap3625_checked
#print axioms fusedMap3625_checked
#print axioms certified3625
def sourceMap3625swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3625swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3625swap_checked : acceptsGraphIso
    (source (graph core3625) (root 8) 6 0) DegreeTwoThreeSpectrum6603.graph sourceMap3625swap=true := by decide +kernel
theorem fusedMap3625swap_checked : acceptsGraphIso
    (fused (graph core3625) (root 8) 6 0) DegreeTwoThreeSpectrum5485.graph fusedMap3625swap=true := by decide +kernel
theorem certified3625swap : Certified (graph core3625) (root 8) 6 0 :=
  of_native_maps core3625 DegreeTwoThreeSpectrum6603.graph DegreeTwoThreeSpectrum5485.graph
    sourceMap3625swap fusedMap3625swap sourceMap3625swap_checked fusedMap3625swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3625
#print axioms sourceMap3625swap_checked
#print axioms fusedMap3625swap_checked
#print axioms certified3625swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
