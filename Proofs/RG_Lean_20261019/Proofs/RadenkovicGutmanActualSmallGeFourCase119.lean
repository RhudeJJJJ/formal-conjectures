/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons07
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core119 : Family 8 := level8.get ⟨187,by decide⟩
def sourceMap119 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,9,10,11,4,5,6,7,8,2,3] (sourceLabel 8 0 1 v)
def fusedMap119 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,8,9,10,11,4,5,6,7,1,2,3] (fusedLabel 8 0 1 v)
theorem sourceMap119_checked : acceptsGraphIso
    (source (graph core119) (root 8) 0 1) SmallGeFourSpectrum180.graph
      sourceMap119=true := by decide +kernel
theorem fusedMap119_checked : acceptsGraphIso
    (fused (graph core119) (root 8) 0 1) SmallGeFourSpectrum108.graph
      fusedMap119=true := by decide +kernel
theorem certified119 : Certified (graph core119) (root 8) 0 1 :=
  of_native_maps core119 SmallGeFourSpectrum180.graph SmallGeFourSpectrum108.graph
    sourceMap119 fusedMap119 sourceMap119_checked fusedMap119_checked
    SmallGeFourComparisons.comparison119
#print axioms sourceMap119_checked
#print axioms fusedMap119_checked
#print axioms certified119
def sourceMap119swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,4,5,6,7,2,3,8] (sourceLabel 8 1 0 v)
def fusedMap119swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,8,9,10,11,4,5,6,7,1,2,3] (fusedLabel 8 1 0 v)
theorem sourceMap119swap_checked : acceptsGraphIso
    (source (graph core119) (root 8) 1 0) SmallGeFourSpectrum180.graph
      sourceMap119swap=true := by decide +kernel
theorem fusedMap119swap_checked : acceptsGraphIso
    (fused (graph core119) (root 8) 1 0) SmallGeFourSpectrum108.graph
      fusedMap119swap=true := by decide +kernel
theorem certified119swap : Certified (graph core119) (root 8) 1 0 :=
  of_native_maps core119 SmallGeFourSpectrum180.graph SmallGeFourSpectrum108.graph
    sourceMap119swap fusedMap119swap sourceMap119swap_checked fusedMap119swap_checked
    SmallGeFourComparisons.comparison119
#print axioms sourceMap119swap_checked
#print axioms fusedMap119swap_checked
#print axioms certified119swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
