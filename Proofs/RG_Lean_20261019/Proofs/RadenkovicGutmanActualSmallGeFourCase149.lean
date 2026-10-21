/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons08
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core149 : Family 8 := level8.get ⟨274,by decide⟩
def sourceMap149 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,7,8] (sourceLabel 8 0 1 v)
def fusedMap149 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap149_checked : acceptsGraphIso
    (source (graph core149) (root 8) 0 1) SmallGeFourSpectrum220.graph
      sourceMap149=true := by decide +kernel
theorem fusedMap149_checked : acceptsGraphIso
    (fused (graph core149) (root 8) 0 1) SmallGeFourSpectrum131.graph
      fusedMap149=true := by decide +kernel
theorem certified149 : Certified (graph core149) (root 8) 0 1 :=
  of_native_maps core149 SmallGeFourSpectrum220.graph SmallGeFourSpectrum131.graph
    sourceMap149 fusedMap149 sourceMap149_checked fusedMap149_checked
    SmallGeFourComparisons.comparison149
#print axioms sourceMap149_checked
#print axioms fusedMap149_checked
#print axioms certified149
def sourceMap149swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,9,10,7,8,11] (sourceLabel 8 1 0 v)
def fusedMap149swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap149swap_checked : acceptsGraphIso
    (source (graph core149) (root 8) 1 0) SmallGeFourSpectrum220.graph
      sourceMap149swap=true := by decide +kernel
theorem fusedMap149swap_checked : acceptsGraphIso
    (fused (graph core149) (root 8) 1 0) SmallGeFourSpectrum131.graph
      fusedMap149swap=true := by decide +kernel
theorem certified149swap : Certified (graph core149) (root 8) 1 0 :=
  of_native_maps core149 SmallGeFourSpectrum220.graph SmallGeFourSpectrum131.graph
    sourceMap149swap fusedMap149swap sourceMap149swap_checked fusedMap149swap_checked
    SmallGeFourComparisons.comparison149
#print axioms sourceMap149swap_checked
#print axioms fusedMap149swap_checked
#print axioms certified149swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
