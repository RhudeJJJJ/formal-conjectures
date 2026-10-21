/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons00
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core008 : Family 4 := level4.get ⟨8,by decide⟩
def sourceMap008 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,4,5,6,7,2,3,0,8,9,10] (sourceLabel 4 1 3 v)
def fusedMap008 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (fusedLabel 4 1 3 v)
theorem sourceMap008_checked : acceptsGraphIso
    (source (graph core008) (root 4) 1 3) SmallGeFourSpectrum062.graph
      sourceMap008=true := by decide +kernel
theorem fusedMap008_checked : acceptsGraphIso
    (fused (graph core008) (root 4) 1 3) SmallGeFourSpectrum037.graph
      fusedMap008=true := by decide +kernel
theorem certified008 : Certified (graph core008) (root 4) 1 3 :=
  of_native_maps core008 SmallGeFourSpectrum062.graph SmallGeFourSpectrum037.graph
    sourceMap008 fusedMap008 sourceMap008_checked fusedMap008_checked
    SmallGeFourComparisons.comparison008
#print axioms sourceMap008_checked
#print axioms fusedMap008_checked
#print axioms certified008
def sourceMap008swap : (Vertices 4 ⊕ Fin 4 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,4,5,6,7,0,8,9,10,2,3] (sourceLabel 4 3 1 v)
def fusedMap008swap : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (fusedLabel 4 3 1 v)
theorem sourceMap008swap_checked : acceptsGraphIso
    (source (graph core008) (root 4) 3 1) SmallGeFourSpectrum062.graph
      sourceMap008swap=true := by decide +kernel
theorem fusedMap008swap_checked : acceptsGraphIso
    (fused (graph core008) (root 4) 3 1) SmallGeFourSpectrum037.graph
      fusedMap008swap=true := by decide +kernel
theorem certified008swap : Certified (graph core008) (root 4) 3 1 :=
  of_native_maps core008 SmallGeFourSpectrum062.graph SmallGeFourSpectrum037.graph
    sourceMap008swap fusedMap008swap sourceMap008swap_checked fusedMap008swap_checked
    SmallGeFourComparisons.comparison008
#print axioms sourceMap008swap_checked
#print axioms fusedMap008swap_checked
#print axioms certified008swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
