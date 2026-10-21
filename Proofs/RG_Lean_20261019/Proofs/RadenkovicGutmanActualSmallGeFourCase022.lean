/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons01
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core022 : Family 5 := level5.get ⟨19,by decide⟩
def sourceMap022 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 5 0 1 v)
def fusedMap022 : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![1,2,3,4,5,6,0,7,8] (fusedLabel 5 0 1 v)
theorem sourceMap022_checked : acceptsGraphIso
    (source (graph core022) (root 5) 0 1) SmallGeFourSpectrum008.graph
      sourceMap022=true := by decide +kernel
theorem fusedMap022_checked : acceptsGraphIso
    (fused (graph core022) (root 5) 0 1) SmallGeFourSpectrum010.graph
      fusedMap022=true := by decide +kernel
theorem certified022 : Certified (graph core022) (root 5) 0 1 :=
  of_native_maps core022 SmallGeFourSpectrum008.graph SmallGeFourSpectrum010.graph
    sourceMap022 fusedMap022 sourceMap022_checked fusedMap022_checked
    SmallGeFourComparisons.comparison022
#print axioms sourceMap022_checked
#print axioms fusedMap022_checked
#print axioms certified022
def sourceMap022swap : (Vertices 5 ⊕ Fin 2 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,7,8,6] (sourceLabel 5 1 0 v)
def fusedMap022swap : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![1,2,3,4,5,6,0,7,8] (fusedLabel 5 1 0 v)
theorem sourceMap022swap_checked : acceptsGraphIso
    (source (graph core022) (root 5) 1 0) SmallGeFourSpectrum008.graph
      sourceMap022swap=true := by decide +kernel
theorem fusedMap022swap_checked : acceptsGraphIso
    (fused (graph core022) (root 5) 1 0) SmallGeFourSpectrum010.graph
      fusedMap022swap=true := by decide +kernel
theorem certified022swap : Certified (graph core022) (root 5) 1 0 :=
  of_native_maps core022 SmallGeFourSpectrum008.graph SmallGeFourSpectrum010.graph
    sourceMap022swap fusedMap022swap sourceMap022swap_checked fusedMap022swap_checked
    SmallGeFourComparisons.comparison022
#print axioms sourceMap022swap_checked
#print axioms fusedMap022swap_checked
#print axioms certified022swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
