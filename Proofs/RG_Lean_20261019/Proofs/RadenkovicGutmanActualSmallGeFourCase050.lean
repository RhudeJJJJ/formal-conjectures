/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons02
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core050 : Family 6 := level6.get ⟨46,by decide⟩
def sourceMap050 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 0 2 v)
def fusedMap050 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap050_checked : acceptsGraphIso
    (source (graph core050) (root 6) 0 2) SmallGeFourSpectrum060.graph
      sourceMap050=true := by decide +kernel
theorem fusedMap050_checked : acceptsGraphIso
    (fused (graph core050) (root 6) 0 2) SmallGeFourSpectrum062.graph
      fusedMap050=true := by decide +kernel
theorem certified050 : Certified (graph core050) (root 6) 0 2 :=
  of_native_maps core050 SmallGeFourSpectrum060.graph SmallGeFourSpectrum062.graph
    sourceMap050 fusedMap050 sourceMap050_checked fusedMap050_checked
    SmallGeFourComparisons.comparison050
#print axioms sourceMap050_checked
#print axioms fusedMap050_checked
#print axioms certified050
def sourceMap050swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,7] (sourceLabel 6 2 0 v)
def fusedMap050swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap050swap_checked : acceptsGraphIso
    (source (graph core050) (root 6) 2 0) SmallGeFourSpectrum060.graph
      sourceMap050swap=true := by decide +kernel
theorem fusedMap050swap_checked : acceptsGraphIso
    (fused (graph core050) (root 6) 2 0) SmallGeFourSpectrum062.graph
      fusedMap050swap=true := by decide +kernel
theorem certified050swap : Certified (graph core050) (root 6) 2 0 :=
  of_native_maps core050 SmallGeFourSpectrum060.graph SmallGeFourSpectrum062.graph
    sourceMap050swap fusedMap050swap sourceMap050swap_checked fusedMap050swap_checked
    SmallGeFourComparisons.comparison050
#print axioms sourceMap050swap_checked
#print axioms fusedMap050swap_checked
#print axioms certified050swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
