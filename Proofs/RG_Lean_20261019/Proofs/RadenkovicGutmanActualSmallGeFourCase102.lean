/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons06
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core102 : Family 7 := level7.get ⟨113,by decide⟩
def sourceMap102 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 0 2 v)
def fusedMap102 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap102_checked : acceptsGraphIso
    (source (graph core102) (root 7) 0 2) SmallGeFourSpectrum178.graph
      sourceMap102=true := by decide +kernel
theorem fusedMap102_checked : acceptsGraphIso
    (fused (graph core102) (root 7) 0 2) SmallGeFourSpectrum180.graph
      fusedMap102=true := by decide +kernel
theorem certified102 : Certified (graph core102) (root 7) 0 2 :=
  of_native_maps core102 SmallGeFourSpectrum178.graph SmallGeFourSpectrum180.graph
    sourceMap102 fusedMap102 sourceMap102_checked fusedMap102_checked
    SmallGeFourComparisons.comparison102
#print axioms sourceMap102_checked
#print axioms fusedMap102_checked
#print axioms certified102
def sourceMap102swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,8] (sourceLabel 7 2 0 v)
def fusedMap102swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap102swap_checked : acceptsGraphIso
    (source (graph core102) (root 7) 2 0) SmallGeFourSpectrum178.graph
      sourceMap102swap=true := by decide +kernel
theorem fusedMap102swap_checked : acceptsGraphIso
    (fused (graph core102) (root 7) 2 0) SmallGeFourSpectrum180.graph
      fusedMap102swap=true := by decide +kernel
theorem certified102swap : Certified (graph core102) (root 7) 2 0 :=
  of_native_maps core102 SmallGeFourSpectrum178.graph SmallGeFourSpectrum180.graph
    sourceMap102swap fusedMap102swap sourceMap102swap_checked fusedMap102swap_checked
    SmallGeFourComparisons.comparison102
#print axioms sourceMap102swap_checked
#print axioms fusedMap102swap_checked
#print axioms certified102swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
