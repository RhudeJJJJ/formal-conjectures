/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons01
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core025 : Family 5 := level5.get ⟨19,by decide⟩
def sourceMap025 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 5) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11] (sourceLabel 5 0 4 v)
def fusedMap025 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 0 4 v)
theorem sourceMap025_checked : acceptsGraphIso
    (source (graph core025) (root 5) 0 4) SmallGeFourSpectrum116.graph
      sourceMap025=true := by decide +kernel
theorem fusedMap025_checked : acceptsGraphIso
    (fused (graph core025) (root 5) 0 4) SmallGeFourSpectrum093.graph
      fusedMap025=true := by decide +kernel
theorem certified025 : Certified (graph core025) (root 5) 0 4 :=
  of_native_maps core025 SmallGeFourSpectrum116.graph SmallGeFourSpectrum093.graph
    sourceMap025 fusedMap025 sourceMap025_checked fusedMap025_checked
    SmallGeFourComparisons.comparison025
#print axioms sourceMap025_checked
#print axioms fusedMap025_checked
#print axioms certified025
def sourceMap025swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,9,10,11,8] (sourceLabel 5 4 0 v)
def fusedMap025swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 4 0 v)
theorem sourceMap025swap_checked : acceptsGraphIso
    (source (graph core025) (root 5) 4 0) SmallGeFourSpectrum116.graph
      sourceMap025swap=true := by decide +kernel
theorem fusedMap025swap_checked : acceptsGraphIso
    (fused (graph core025) (root 5) 4 0) SmallGeFourSpectrum093.graph
      fusedMap025swap=true := by decide +kernel
theorem certified025swap : Certified (graph core025) (root 5) 4 0 :=
  of_native_maps core025 SmallGeFourSpectrum116.graph SmallGeFourSpectrum093.graph
    sourceMap025swap fusedMap025swap sourceMap025swap_checked fusedMap025swap_checked
    SmallGeFourComparisons.comparison025
#print axioms sourceMap025swap_checked
#print axioms fusedMap025swap_checked
#print axioms certified025swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
