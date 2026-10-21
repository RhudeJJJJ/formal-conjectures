/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons08
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core145 : Family 8 := level8.get ⟨263,by decide⟩
def sourceMap145 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,9,10,11,3,4,5,6,7,8,1,2] (sourceLabel 8 0 1 v)
def fusedMap145 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,7,8,9,10,11,4,5,6] (fusedLabel 8 0 1 v)
theorem sourceMap145_checked : acceptsGraphIso
    (source (graph core145) (root 8) 0 1) SmallGeFourSpectrum178.graph
      sourceMap145=true := by decide +kernel
theorem fusedMap145_checked : acceptsGraphIso
    (fused (graph core145) (root 8) 0 1) SmallGeFourSpectrum196.graph
      fusedMap145=true := by decide +kernel
theorem certified145 : Certified (graph core145) (root 8) 0 1 :=
  of_native_maps core145 SmallGeFourSpectrum178.graph SmallGeFourSpectrum196.graph
    sourceMap145 fusedMap145 sourceMap145_checked fusedMap145_checked
    SmallGeFourComparisons.comparison145
#print axioms sourceMap145_checked
#print axioms fusedMap145_checked
#print axioms certified145
def sourceMap145swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,9,10,11,3,4,5,6,7,1,2,8] (sourceLabel 8 1 0 v)
def fusedMap145swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,7,8,9,10,11,4,5,6] (fusedLabel 8 1 0 v)
theorem sourceMap145swap_checked : acceptsGraphIso
    (source (graph core145) (root 8) 1 0) SmallGeFourSpectrum178.graph
      sourceMap145swap=true := by decide +kernel
theorem fusedMap145swap_checked : acceptsGraphIso
    (fused (graph core145) (root 8) 1 0) SmallGeFourSpectrum196.graph
      fusedMap145swap=true := by decide +kernel
theorem certified145swap : Certified (graph core145) (root 8) 1 0 :=
  of_native_maps core145 SmallGeFourSpectrum178.graph SmallGeFourSpectrum196.graph
    sourceMap145swap fusedMap145swap sourceMap145swap_checked fusedMap145swap_checked
    SmallGeFourComparisons.comparison145
#print axioms sourceMap145swap_checked
#print axioms fusedMap145swap_checked
#print axioms certified145swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
