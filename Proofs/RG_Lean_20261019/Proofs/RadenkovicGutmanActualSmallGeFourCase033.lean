/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons01
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core033 : Family 6 := level6.get ⟨36,by decide⟩
def sourceMap033 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 0 3 v)
def fusedMap033 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap033_checked : acceptsGraphIso
    (source (graph core033) (root 6) 0 3) SmallGeFourSpectrum108.graph
      sourceMap033=true := by decide +kernel
theorem fusedMap033_checked : acceptsGraphIso
    (fused (graph core033) (root 6) 0 3) SmallGeFourSpectrum110.graph
      fusedMap033=true := by decide +kernel
theorem certified033 : Certified (graph core033) (root 6) 0 3 :=
  of_native_maps core033 SmallGeFourSpectrum108.graph SmallGeFourSpectrum110.graph
    sourceMap033 fusedMap033 sourceMap033_checked fusedMap033_checked
    SmallGeFourComparisons.comparison033
#print axioms sourceMap033_checked
#print axioms fusedMap033_checked
#print axioms certified033
def sourceMap033swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,7] (sourceLabel 6 3 0 v)
def fusedMap033swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap033swap_checked : acceptsGraphIso
    (source (graph core033) (root 6) 3 0) SmallGeFourSpectrum108.graph
      sourceMap033swap=true := by decide +kernel
theorem fusedMap033swap_checked : acceptsGraphIso
    (fused (graph core033) (root 6) 3 0) SmallGeFourSpectrum110.graph
      fusedMap033swap=true := by decide +kernel
theorem certified033swap : Certified (graph core033) (root 6) 3 0 :=
  of_native_maps core033 SmallGeFourSpectrum108.graph SmallGeFourSpectrum110.graph
    sourceMap033swap fusedMap033swap sourceMap033swap_checked fusedMap033swap_checked
    SmallGeFourComparisons.comparison033
#print axioms sourceMap033swap_checked
#print axioms fusedMap033swap_checked
#print axioms certified033swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
