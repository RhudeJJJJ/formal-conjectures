/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4020 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap4020 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,9,7,8,1,0,10,11,12,13,14,15] (sourceLabel 5 1 7 v)
def fusedMap4020 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 1 7 v)
theorem sourceMap4020_checked : acceptsGraphIso
    (source (graph core4020) (root 5) 1 7) DegreeTwoThreeSpectrum3943.graph sourceMap4020=true := by decide +kernel
theorem fusedMap4020_checked : acceptsGraphIso
    (fused (graph core4020) (root 5) 1 7) DegreeTwoThreeSpectrum3856.graph fusedMap4020=true := by decide +kernel
theorem certified4020 : Certified (graph core4020) (root 5) 1 7 :=
  of_native_maps core4020 DegreeTwoThreeSpectrum3943.graph DegreeTwoThreeSpectrum3856.graph
    sourceMap4020 fusedMap4020 sourceMap4020_checked fusedMap4020_checked
    DegreeTwoThreeFiniteComparisons.comparison4020
#print axioms sourceMap4020_checked
#print axioms fusedMap4020_checked
#print axioms certified4020
def sourceMap4020swap : (Vertices 5 ⊕ Fin 8 ⊕ Fin 2) → Fin 16 :=
  fun v => ![2,3,4,5,6,9,1,0,10,11,12,13,14,15,7,8] (sourceLabel 5 7 1 v)
def fusedMap4020swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 7 1 v)
theorem sourceMap4020swap_checked : acceptsGraphIso
    (source (graph core4020) (root 5) 7 1) DegreeTwoThreeSpectrum3943.graph sourceMap4020swap=true := by decide +kernel
theorem fusedMap4020swap_checked : acceptsGraphIso
    (fused (graph core4020) (root 5) 7 1) DegreeTwoThreeSpectrum3856.graph fusedMap4020swap=true := by decide +kernel
theorem certified4020swap : Certified (graph core4020) (root 5) 7 1 :=
  of_native_maps core4020 DegreeTwoThreeSpectrum3943.graph DegreeTwoThreeSpectrum3856.graph
    sourceMap4020swap fusedMap4020swap sourceMap4020swap_checked fusedMap4020swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4020
#print axioms sourceMap4020swap_checked
#print axioms fusedMap4020swap_checked
#print axioms certified4020swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
