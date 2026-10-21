/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons00
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core009 : Family 4 := level4.get ⟨8,by decide⟩
def sourceMap009 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,4,5,6,7,2,3,0,8,9,10,11] (sourceLabel 4 1 4 v)
def fusedMap009 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11] (fusedLabel 4 1 4 v)
theorem sourceMap009_checked : acceptsGraphIso
    (source (graph core009) (root 4) 1 4) SmallGeFourSpectrum100.graph
      sourceMap009=true := by decide +kernel
theorem fusedMap009_checked : acceptsGraphIso
    (fused (graph core009) (root 4) 1 4) SmallGeFourSpectrum094.graph
      fusedMap009=true := by decide +kernel
theorem certified009 : Certified (graph core009) (root 4) 1 4 :=
  of_native_maps core009 SmallGeFourSpectrum100.graph SmallGeFourSpectrum094.graph
    sourceMap009 fusedMap009 sourceMap009_checked fusedMap009_checked
    SmallGeFourComparisons.comparison009
#print axioms sourceMap009_checked
#print axioms fusedMap009_checked
#print axioms certified009
def sourceMap009swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,4,5,6,7,0,8,9,10,11,2,3] (sourceLabel 4 4 1 v)
def fusedMap009swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11] (fusedLabel 4 4 1 v)
theorem sourceMap009swap_checked : acceptsGraphIso
    (source (graph core009) (root 4) 4 1) SmallGeFourSpectrum100.graph
      sourceMap009swap=true := by decide +kernel
theorem fusedMap009swap_checked : acceptsGraphIso
    (fused (graph core009) (root 4) 4 1) SmallGeFourSpectrum094.graph
      fusedMap009swap=true := by decide +kernel
theorem certified009swap : Certified (graph core009) (root 4) 4 1 :=
  of_native_maps core009 SmallGeFourSpectrum100.graph SmallGeFourSpectrum094.graph
    sourceMap009swap fusedMap009swap sourceMap009swap_checked fusedMap009swap_checked
    SmallGeFourComparisons.comparison009
#print axioms sourceMap009swap_checked
#print axioms fusedMap009swap_checked
#print axioms certified009swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
