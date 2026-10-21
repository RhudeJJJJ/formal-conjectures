/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons12
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core215 : Family 9 := level9.get ⟨666,by decide⟩
def sourceMap215 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap215 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap215_checked : acceptsGraphIso
    (source (graph core215) (root 9) 0 0) SmallGeFourSpectrum191.graph
      sourceMap215=true := by decide +kernel
theorem fusedMap215_checked : acceptsGraphIso
    (fused (graph core215) (root 9) 0 0) SmallGeFourSpectrum190.graph
      fusedMap215=true := by decide +kernel
theorem certified215 : Certified (graph core215) (root 9) 0 0 :=
  of_native_maps core215 SmallGeFourSpectrum191.graph SmallGeFourSpectrum190.graph
    sourceMap215 fusedMap215 sourceMap215_checked fusedMap215_checked
    SmallGeFourComparisons.comparison215
#print axioms sourceMap215_checked
#print axioms fusedMap215_checked
#print axioms certified215
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
