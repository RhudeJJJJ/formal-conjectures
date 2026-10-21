/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons01
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core032 : Family 6 := level6.get ⟨36,by decide⟩
def sourceMap032 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,7,8,9,10,4,5,6] (sourceLabel 6 0 2 v)
def fusedMap032 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap032_checked : acceptsGraphIso
    (source (graph core032) (root 6) 0 2) SmallGeFourSpectrum068.graph
      sourceMap032=true := by decide +kernel
theorem fusedMap032_checked : acceptsGraphIso
    (fused (graph core032) (root 6) 0 2) SmallGeFourSpectrum039.graph
      fusedMap032=true := by decide +kernel
theorem certified032 : Certified (graph core032) (root 6) 0 2 :=
  of_native_maps core032 SmallGeFourSpectrum068.graph SmallGeFourSpectrum039.graph
    sourceMap032 fusedMap032 sourceMap032_checked fusedMap032_checked
    SmallGeFourComparisons.comparison032
#print axioms sourceMap032_checked
#print axioms fusedMap032_checked
#print axioms certified032
def sourceMap032swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,7,8,9,4,5,6,10] (sourceLabel 6 2 0 v)
def fusedMap032swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap032swap_checked : acceptsGraphIso
    (source (graph core032) (root 6) 2 0) SmallGeFourSpectrum068.graph
      sourceMap032swap=true := by decide +kernel
theorem fusedMap032swap_checked : acceptsGraphIso
    (fused (graph core032) (root 6) 2 0) SmallGeFourSpectrum039.graph
      fusedMap032swap=true := by decide +kernel
theorem certified032swap : Certified (graph core032) (root 6) 2 0 :=
  of_native_maps core032 SmallGeFourSpectrum068.graph SmallGeFourSpectrum039.graph
    sourceMap032swap fusedMap032swap sourceMap032swap_checked fusedMap032swap_checked
    SmallGeFourComparisons.comparison032
#print axioms sourceMap032swap_checked
#print axioms fusedMap032swap_checked
#print axioms certified032swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
