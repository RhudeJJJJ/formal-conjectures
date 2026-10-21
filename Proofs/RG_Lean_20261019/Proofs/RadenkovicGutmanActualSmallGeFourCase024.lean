/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons01
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core024 : Family 5 := level5.get ⟨19,by decide⟩
def sourceMap024 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (sourceLabel 5 0 3 v)
def fusedMap024 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10] (fusedLabel 5 0 3 v)
theorem sourceMap024_checked : acceptsGraphIso
    (source (graph core024) (root 5) 0 3) SmallGeFourSpectrum040.graph
      sourceMap024=true := by decide +kernel
theorem fusedMap024_checked : acceptsGraphIso
    (fused (graph core024) (root 5) 0 3) SmallGeFourSpectrum044.graph
      fusedMap024=true := by decide +kernel
theorem certified024 : Certified (graph core024) (root 5) 0 3 :=
  of_native_maps core024 SmallGeFourSpectrum040.graph SmallGeFourSpectrum044.graph
    sourceMap024 fusedMap024 sourceMap024_checked fusedMap024_checked
    SmallGeFourComparisons.comparison024
#print axioms sourceMap024_checked
#print axioms fusedMap024_checked
#print axioms certified024
def sourceMap024swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,7] (sourceLabel 5 3 0 v)
def fusedMap024swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10] (fusedLabel 5 3 0 v)
theorem sourceMap024swap_checked : acceptsGraphIso
    (source (graph core024) (root 5) 3 0) SmallGeFourSpectrum040.graph
      sourceMap024swap=true := by decide +kernel
theorem fusedMap024swap_checked : acceptsGraphIso
    (fused (graph core024) (root 5) 3 0) SmallGeFourSpectrum044.graph
      fusedMap024swap=true := by decide +kernel
theorem certified024swap : Certified (graph core024) (root 5) 3 0 :=
  of_native_maps core024 SmallGeFourSpectrum040.graph SmallGeFourSpectrum044.graph
    sourceMap024swap fusedMap024swap sourceMap024swap_checked fusedMap024swap_checked
    SmallGeFourComparisons.comparison024
#print axioms sourceMap024swap_checked
#print axioms fusedMap024swap_checked
#print axioms certified024swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
