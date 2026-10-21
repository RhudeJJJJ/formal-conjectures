/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons05
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core098 : Family 7 := level7.get ⟨112,by decide⟩
def sourceMap098 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 0 2 v)
def fusedMap098 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap098_checked : acceptsGraphIso
    (source (graph core098) (root 7) 0 2) SmallGeFourSpectrum167.graph
      sourceMap098=true := by decide +kernel
theorem fusedMap098_checked : acceptsGraphIso
    (fused (graph core098) (root 7) 0 2) SmallGeFourSpectrum169.graph
      fusedMap098=true := by decide +kernel
theorem certified098 : Certified (graph core098) (root 7) 0 2 :=
  of_native_maps core098 SmallGeFourSpectrum167.graph SmallGeFourSpectrum169.graph
    sourceMap098 fusedMap098 sourceMap098_checked fusedMap098_checked
    SmallGeFourComparisons.comparison098
#print axioms sourceMap098_checked
#print axioms fusedMap098_checked
#print axioms certified098
def sourceMap098swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,8] (sourceLabel 7 2 0 v)
def fusedMap098swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap098swap_checked : acceptsGraphIso
    (source (graph core098) (root 7) 2 0) SmallGeFourSpectrum167.graph
      sourceMap098swap=true := by decide +kernel
theorem fusedMap098swap_checked : acceptsGraphIso
    (fused (graph core098) (root 7) 2 0) SmallGeFourSpectrum169.graph
      fusedMap098swap=true := by decide +kernel
theorem certified098swap : Certified (graph core098) (root 7) 2 0 :=
  of_native_maps core098 SmallGeFourSpectrum167.graph SmallGeFourSpectrum169.graph
    sourceMap098swap fusedMap098swap sourceMap098swap_checked fusedMap098swap_checked
    SmallGeFourComparisons.comparison098
#print axioms sourceMap098swap_checked
#print axioms fusedMap098swap_checked
#print axioms certified098swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
