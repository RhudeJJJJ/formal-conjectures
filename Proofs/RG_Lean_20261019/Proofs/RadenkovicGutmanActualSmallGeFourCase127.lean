/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons07
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core127 : Family 8 := level8.get ⟨229,by decide⟩
def sourceMap127 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![4,0,1,2,3,7,8,9,10,11,5,6] (sourceLabel 8 0 1 v)
def fusedMap127 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,8,9,10,11,5,6,7] (fusedLabel 8 0 1 v)
theorem sourceMap127_checked : acceptsGraphIso
    (source (graph core127) (root 8) 0 1) SmallGeFourSpectrum158.graph
      sourceMap127=true := by decide +kernel
theorem fusedMap127_checked : acceptsGraphIso
    (fused (graph core127) (root 8) 0 1) SmallGeFourSpectrum162.graph
      fusedMap127=true := by decide +kernel
theorem certified127 : Certified (graph core127) (root 8) 0 1 :=
  of_native_maps core127 SmallGeFourSpectrum158.graph SmallGeFourSpectrum162.graph
    sourceMap127 fusedMap127 sourceMap127_checked fusedMap127_checked
    SmallGeFourComparisons.comparison127
#print axioms sourceMap127_checked
#print axioms fusedMap127_checked
#print axioms certified127
def sourceMap127swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![4,0,1,2,3,7,8,9,10,5,6,11] (sourceLabel 8 1 0 v)
def fusedMap127swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,8,9,10,11,5,6,7] (fusedLabel 8 1 0 v)
theorem sourceMap127swap_checked : acceptsGraphIso
    (source (graph core127) (root 8) 1 0) SmallGeFourSpectrum158.graph
      sourceMap127swap=true := by decide +kernel
theorem fusedMap127swap_checked : acceptsGraphIso
    (fused (graph core127) (root 8) 1 0) SmallGeFourSpectrum162.graph
      fusedMap127swap=true := by decide +kernel
theorem certified127swap : Certified (graph core127) (root 8) 1 0 :=
  of_native_maps core127 SmallGeFourSpectrum158.graph SmallGeFourSpectrum162.graph
    sourceMap127swap fusedMap127swap sourceMap127swap_checked fusedMap127swap_checked
    SmallGeFourComparisons.comparison127
#print axioms sourceMap127swap_checked
#print axioms fusedMap127swap_checked
#print axioms certified127swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
