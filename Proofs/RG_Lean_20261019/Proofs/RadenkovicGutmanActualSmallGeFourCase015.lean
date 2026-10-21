/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons00
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core015 : Family 5 := level5.get ⟨18,by decide⟩
def sourceMap015 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (sourceLabel 5 0 3 v)
def fusedMap015 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 0 3 v)
theorem sourceMap015_checked : acceptsGraphIso
    (source (graph core015) (root 5) 0 3) SmallGeFourSpectrum062.graph
      sourceMap015=true := by decide +kernel
theorem fusedMap015_checked : acceptsGraphIso
    (fused (graph core015) (root 5) 0 3) SmallGeFourSpectrum038.graph
      fusedMap015=true := by decide +kernel
theorem certified015 : Certified (graph core015) (root 5) 0 3 :=
  of_native_maps core015 SmallGeFourSpectrum062.graph SmallGeFourSpectrum038.graph
    sourceMap015 fusedMap015 sourceMap015_checked fusedMap015_checked
    SmallGeFourComparisons.comparison015
#print axioms sourceMap015_checked
#print axioms fusedMap015_checked
#print axioms certified015
def sourceMap015swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,7] (sourceLabel 5 3 0 v)
def fusedMap015swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 3 0 v)
theorem sourceMap015swap_checked : acceptsGraphIso
    (source (graph core015) (root 5) 3 0) SmallGeFourSpectrum062.graph
      sourceMap015swap=true := by decide +kernel
theorem fusedMap015swap_checked : acceptsGraphIso
    (fused (graph core015) (root 5) 3 0) SmallGeFourSpectrum038.graph
      fusedMap015swap=true := by decide +kernel
theorem certified015swap : Certified (graph core015) (root 5) 3 0 :=
  of_native_maps core015 SmallGeFourSpectrum062.graph SmallGeFourSpectrum038.graph
    sourceMap015swap fusedMap015swap sourceMap015swap_checked fusedMap015swap_checked
    SmallGeFourComparisons.comparison015
#print axioms sourceMap015swap_checked
#print axioms fusedMap015swap_checked
#print axioms certified015swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
