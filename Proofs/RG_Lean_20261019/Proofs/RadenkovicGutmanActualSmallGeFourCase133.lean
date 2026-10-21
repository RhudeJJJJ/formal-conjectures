/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons07
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core133 : Family 8 := level8.get ⟨253,by decide⟩
def sourceMap133 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,5,6,7,3,4] (sourceLabel 8 0 1 v)
def fusedMap133 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,8,9,10,11,5,6,7] (fusedLabel 8 0 1 v)
theorem sourceMap133_checked : acceptsGraphIso
    (source (graph core133) (root 8) 0 1) SmallGeFourSpectrum168.graph
      sourceMap133=true := by decide +kernel
theorem fusedMap133_checked : acceptsGraphIso
    (fused (graph core133) (root 8) 0 1) SmallGeFourSpectrum190.graph
      fusedMap133=true := by decide +kernel
theorem certified133 : Certified (graph core133) (root 8) 0 1 :=
  of_native_maps core133 SmallGeFourSpectrum168.graph SmallGeFourSpectrum190.graph
    sourceMap133 fusedMap133 sourceMap133_checked fusedMap133_checked
    SmallGeFourComparisons.comparison133
#print axioms sourceMap133_checked
#print axioms fusedMap133_checked
#print axioms certified133
def sourceMap133swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,5,6,3,4,7] (sourceLabel 8 1 0 v)
def fusedMap133swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,8,9,10,11,5,6,7] (fusedLabel 8 1 0 v)
theorem sourceMap133swap_checked : acceptsGraphIso
    (source (graph core133) (root 8) 1 0) SmallGeFourSpectrum168.graph
      sourceMap133swap=true := by decide +kernel
theorem fusedMap133swap_checked : acceptsGraphIso
    (fused (graph core133) (root 8) 1 0) SmallGeFourSpectrum190.graph
      fusedMap133swap=true := by decide +kernel
theorem certified133swap : Certified (graph core133) (root 8) 1 0 :=
  of_native_maps core133 SmallGeFourSpectrum168.graph SmallGeFourSpectrum190.graph
    sourceMap133swap fusedMap133swap sourceMap133swap_checked fusedMap133swap_checked
    SmallGeFourComparisons.comparison133
#print axioms sourceMap133swap_checked
#print axioms fusedMap133swap_checked
#print axioms certified133swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
