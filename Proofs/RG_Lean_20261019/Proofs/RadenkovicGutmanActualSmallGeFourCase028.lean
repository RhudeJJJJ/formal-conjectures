/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons01
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core028 : Family 5 := level5.get ⟨19,by decide⟩
def sourceMap028 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,4,5,6,7,8,2,3,0,9,10,11] (sourceLabel 5 1 3 v)
def fusedMap028 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 1 3 v)
theorem sourceMap028_checked : acceptsGraphIso
    (source (graph core028) (root 5) 1 3) SmallGeFourSpectrum180.graph
      sourceMap028=true := by decide +kernel
theorem fusedMap028_checked : acceptsGraphIso
    (fused (graph core028) (root 5) 1 3) SmallGeFourSpectrum093.graph
      fusedMap028=true := by decide +kernel
theorem certified028 : Certified (graph core028) (root 5) 1 3 :=
  of_native_maps core028 SmallGeFourSpectrum180.graph SmallGeFourSpectrum093.graph
    sourceMap028 fusedMap028 sourceMap028_checked fusedMap028_checked
    SmallGeFourComparisons.comparison028
#print axioms sourceMap028_checked
#print axioms fusedMap028_checked
#print axioms certified028
def sourceMap028swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,4,5,6,7,8,0,9,10,11,2,3] (sourceLabel 5 3 1 v)
def fusedMap028swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 3 1 v)
theorem sourceMap028swap_checked : acceptsGraphIso
    (source (graph core028) (root 5) 3 1) SmallGeFourSpectrum180.graph
      sourceMap028swap=true := by decide +kernel
theorem fusedMap028swap_checked : acceptsGraphIso
    (fused (graph core028) (root 5) 3 1) SmallGeFourSpectrum093.graph
      fusedMap028swap=true := by decide +kernel
theorem certified028swap : Certified (graph core028) (root 5) 3 1 :=
  of_native_maps core028 SmallGeFourSpectrum180.graph SmallGeFourSpectrum093.graph
    sourceMap028swap fusedMap028swap sourceMap028swap_checked fusedMap028swap_checked
    SmallGeFourComparisons.comparison028
#print axioms sourceMap028swap_checked
#print axioms fusedMap028swap_checked
#print axioms certified028swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
